/*-------------------------------------------------------------------------
 *
 * semijoin_explain.c
 *		  BloomBridge: make the planner and EXPLAIN understand the
 *		  semijoin rewrite of semijoin.c.
 *
 * Role of this file in the project
 * --------------------------------
 * semijoin.c rewrites "local JOIN foreign" by adding one condition on the
 * foreign table:  key = ANY($1)  or  sjb_contains($1, key). Two problems
 * remain after that rewrite, and this file solves them:
 *
 *   1. The row estimate. The planner cannot look inside $1 (it is only
 *      computed at run time), so it guesses ~10 rows for "= ANY($1)" and
 *      1/3 of the table for sjb_contains. With 10 rows it picks a slow
 *      Nested Loop. pgfdw_apply_semijoin_hint (called from
 *      postgresGetForeignRelSize) replaces that guess with the cost
 *      model's expected rows ("the hint" that semijoin.c fills in).
 *
 *   2. Visibility. EXPLAIN shows our decision ("Semijoin Path",
 *      "Estimated Keys", "Predicted Time"), and EXPLAIN ANALYZE decodes
 *      the parameter that was really sent ("Semijoin Filter: mode=bloom
 *      keys=... m=... k=... bytes_sent=...").
 *
 * IDENTIFICATION
 *		  contrib/postgres_fdw/semijoin_explain.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"
#include <math.h>
#include "access/htup_details.h"
#include "access/sysattr.h"
#include "access/xact.h"
#include "commands/explain_format.h"
#include "commands/explain_state.h"
#include "catalog/pg_class.h"
#include "catalog/pg_operator.h"
#include "catalog/pg_statistic.h"
#include "catalog/pg_type.h"
#include "commands/defrem.h"
#include "commands/extension.h"
#include "foreign/foreign.h"
#include "lib/stringinfo.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/optimizer.h"
#include "optimizer/planner.h"
#include "parser/analyze.h"
#include "parser/parse_func.h"
#include "parser/parser.h"
#include "parser/parsetree.h"
#include "postgres_fdw.h"
#include "rewrite/rewriteManip.h"
#include "utils/builtins.h"
#include "utils/guc.h"
#include "utils/lsyscache.h"
#include "utils/resowner.h"
#include "utils/ruleutils.h"
#include "utils/syscache.h"

/* ------------------------------------------------------------------------
 * Batch 7: the row estimate of the rewritten foreign scan
 * ------------------------------------------------------------------------
 */

/*
 * is_join_column_var
 *
 * What it does: checks that a node is the foreign table's join column.
 * Inputs:  node - an expression; hint - the hint; relid - the foreign
 *          table's number in the planner's range table
 * Output:  true or false
 * Why it exists: our condition always has the join column as one argument.
 */
static bool
is_join_column_var(Node *node, SemijoinHint *hint, Index relid)
{
	Var		   *var;

	if (node == NULL || !IsA(node, Var))
		return false;
	var = (Var *) node;
	return var->varno == relid && var->varattno == hint->foreign_attno &&
		var->varlevelsup == 0;
}

/*
 * is_initplan_param
 *
 * What it does: checks that a node is a PARAM_EXEC parameter, which is
 * what our "(SELECT ...)" has become: the planner turned it into an
 * InitPlan whose result is this parameter.
 * Input:  node - an expression
 * Output: true or false
 * Why it exists: our condition always has it as the other argument.
 */
static bool
is_initplan_param(Node *node)
{
	return node != NULL && IsA(node, Param) &&
		((Param *) node)->paramkind == PARAM_EXEC;
}

/*
 * is_semijoin_clause
 *
 * What it does: recognises OUR condition among the conditions of the
 * foreign table, as the planner sees it:
 *   index path:  join_column = ANY ($n)
 *   filter path: sjb_contains($n, join_column)
 *
 * Inputs:  clause - one condition; hint; relid - see is_join_column_var
 * Output:  true if it is our condition
 *
 * Why it exists: its selectivity is replaced by our expected rows, while
 * all other conditions keep their normal selectivity.
 */
static bool
is_semijoin_clause(Node *clause, SemijoinHint *hint, Index relid)
{
	if (hint->path == SEMIJOIN_PATH_INDEX && IsA(clause, ScalarArrayOpExpr))
	{
		ScalarArrayOpExpr *any_expr = (ScalarArrayOpExpr *) clause;

		return any_expr->opno == Int4EqualOperator && any_expr->useOr &&
			list_length(any_expr->args) == 2 &&
			is_join_column_var((Node *) linitial(any_expr->args), hint, relid) &&
			is_initplan_param((Node *) lsecond(any_expr->args));
	}

	if (hint->path == SEMIJOIN_PATH_FILTER && IsA(clause, FuncExpr))
	{
		FuncExpr   *func = (FuncExpr *) clause;

		return func->funcid == hint->contains_funcid &&
			list_length(func->args) == 2 &&
			is_initplan_param((Node *) linitial(func->args)) &&
			is_join_column_var((Node *) lsecond(func->args), hint, relid);
	}
	return false;
}

/*
 * pgfdw_apply_semijoin_hint
 *
 * What it does: called by postgresGetForeignRelSize, right after
 * PostgreSQL's normal estimate set_baserel_size_estimates. If this is the
 * foreign table our hook rewrote, it replaces the row estimate:
 *     baserel->rows = expected_rows * (selectivity of the OTHER conditions)
 * The planner cannot see inside "= ANY ($n)" (it guesses ~10 rows) or
 * sjb_contains (it guesses 1/3 of the table); our cost model knows better.
 * postgres_fdw derives everything else (fpinfo->rows, retrieved_rows, the
 * per-row costs) from baserel->rows, so this is the only value we change.
 *
 * It does nothing unless ALL of these hold:
 *   - a hint is set (only while our rewritten query is planned),
 *   - its OID is this foreign table's,
 *   - root->query_level == 1: the top-level query, never a subquery,
 *   - our own condition is found among the table's conditions.
 *
 * Inputs:  root - the planner's state; baserel - the foreign table;
 *          foreigntableid - its OID
 * Output:  none (baserel->rows may change)
 *
 * Why it exists: with ~10 estimated rows the planner picked a Nested Loop
 * with a Join Filter at n <= 1000 instead of a Hash Join.
 */
void
pgfdw_apply_semijoin_hint(PlannerInfo *root, RelOptInfo *baserel,
						  Oid foreigntableid)
{
	SemijoinHint *hint = pgfdw_semijoin_hint;
	List	   *other_clauses = NIL;
	bool		found = false;
	Selectivity other_selectivity;
	double		old_rows = baserel->rows;
	ListCell   *cell;

	if (hint == NULL || hint->foreign_relid != foreigntableid ||
		root->query_level != 1)
		return;

	/* split the table's conditions into ours and the others */
	foreach(cell, baserel->baserestrictinfo)
	{
		/* lfirst_node = lfirst, plus a check of the node type */
		RestrictInfo *rinfo = lfirst_node(RestrictInfo, cell);

		if (!found && is_semijoin_clause((Node *) rinfo->clause, hint, baserel->relid))
			found = true;
		else
			other_clauses = lappend(other_clauses, rinfo);
	}
	if (!found)
		return;

	/* the planner's normal selectivity of all the other conditions */
	other_selectivity = clauselist_selectivity(root, other_clauses,
											   baserel->relid, JOIN_INNER, NULL);

	/* clamp_row_est rounds and keeps the estimate at least 1 */
	baserel->rows = clamp_row_est(hint->expected_rows * other_selectivity);

	if (pgfdw_semijoin_verbose)
		ereport(NOTICE,
				(errmsg("semijoin: foreign scan rows %.0f -> %.0f",
						old_rows, baserel->rows)));
}

/* ------------------------------------------------------------------------
 * Batch 7: our decision in EXPLAIN
 * ------------------------------------------------------------------------
 */

/*
 * Positions inside our own list, which postgresGetForeignPlan stores in
 * the ForeignScan's fdw_private at position FdwScanPrivateSemijoin.
 * Only plain node types (Integer, Float) are used, so the plan can be
 * copied and saved like any other plan.
 */
enum SemijoinPrivateIndex
{
	SemijoinPrivatePath,		/* Integer: SEMIJOIN_PATH_INDEX or _FILTER */
	SemijoinPrivateKeys,		/* Float: n_est */
	SemijoinPrivateIndexMs,		/* Float: predicted time, index path */
	SemijoinPrivateFilterMs,	/* Float: predicted time, filter path */
	SemijoinPrivateParamIndex,	/* Integer: our parameter ($n is n-1), or -1 */
};

/*
 * Layout of the 24-byte filter header written by sjbloom (see
 * sjbloom/sjb_filter.h in the project): version uint8, mode uint8,
 * k uint16, nkeys uint32, m uint64, seed uint64. sjbloom writes it with
 * memcpy in the machine's byte order; site A built the filter, so we read
 * it back the same way.
 */
#define SJB_HEADER_SIZE 24
#define SJB_HEADER_VERSION 3
#define SJB_OFFSET_VERSION 0
#define SJB_OFFSET_MODE 1
#define SJB_OFFSET_K 2
#define SJB_OFFSET_NKEYS 4
#define SJB_OFFSET_M 8

/*
 * pgfdw_semijoin_plan_info
 *
 * What it does: called by postgresGetForeignPlan. If our hook rewrote this
 * foreign scan, it returns a small List with the decision (path, n_est,
 * both predicted times) and the position of our parameter among the
 * scan's parameters ($1, $2, ...), so that EXPLAIN can show them later.
 *
 * Inputs:  root, foreignrel - the planner's state and the foreign table
 *          remote_conds     - the conditions sent to site B (RestrictInfos)
 *          params_list      - the parameters of the remote query, in order
 * Output:  the List, or NIL if this scan was not rewritten
 *
 * Why it exists: the hint only lives while the query is planned, but
 * EXPLAIN runs later, from the finished plan. So the values are copied
 * into the plan itself.
 */
List *
pgfdw_semijoin_plan_info(PlannerInfo *root, RelOptInfo *foreignrel,
						 List *remote_conds, List *params_list)
{
	SemijoinHint *hint = pgfdw_semijoin_hint;
	RangeTblEntry *rte;
	Node	   *our_param = NULL;
	int			param_index = -1;
	int			position;
	ListCell   *cell;

	if (hint == NULL || root->query_level != 1 ||
		foreignrel->reloptkind != RELOPT_BASEREL)
		return NIL;

	/* planner_rt_fetch: the range table entry of this relation */
	rte = planner_rt_fetch(foreignrel->relid, root);
	if (rte->relid != hint->foreign_relid)
		return NIL;

	/* find our condition, and in it our parameter */
	foreach(cell, remote_conds)
	{
		RestrictInfo *rinfo = lfirst_node(RestrictInfo, cell);
		List	   *args;

		if (!is_semijoin_clause((Node *) rinfo->clause, hint, foreignrel->relid))
			continue;
		if (IsA(rinfo->clause, ScalarArrayOpExpr))
			args = ((ScalarArrayOpExpr *) rinfo->clause)->args;
		else
			args = ((FuncExpr *) rinfo->clause)->args;
		our_param = (hint->path == SEMIJOIN_PATH_INDEX) ? lsecond(args) : linitial(args);
		break;
	}
	if (our_param == NULL)
		return NIL;				/* our condition is not sent to site B */

	/* its position among the remote query's parameters */
	position = 0;
	foreach(cell, params_list)
	{
		/* equal() compares two node trees */
		if (equal(lfirst(cell), our_param))
		{
			param_index = position;
			break;
		}
		position++;
	}

	/* makeInteger / makeFloat wrap a number as a node (Float keeps text) */
	return list_make5(makeInteger(hint->path),
					  makeFloat(psprintf("%.17g", hint->n_est)),
					  makeFloat(psprintf("%.17g", hint->index_ms)),
					  makeFloat(psprintf("%.17g", hint->filter_ms)),
					  makeInteger(param_index));
}

/*
 * pgfdw_semijoin_info_path / pgfdw_semijoin_info_param_index
 *
 * What they do: read the path and the parameter position back from the
 * List made by pgfdw_semijoin_plan_info.
 * Input:  info - that List
 * Output: the path / the parameter position (-1 = unknown)
 * Why they exist: postgres_fdw.c should not need to know the List's
 * layout.
 */
int
pgfdw_semijoin_info_path(List *info)
{
	return intVal(list_nth(info, SemijoinPrivatePath));
}

int
pgfdw_semijoin_info_param_index(List *info)
{
	return intVal(list_nth(info, SemijoinPrivateParamIndex));
}

/*
 * hex_digit_value
 *
 * What it does: the value 0-15 of one hex digit, or -1 if it is not one.
 * Input:  digit - a character
 * Output: its value, or -1
 * Why it exists: a bytea parameter is sent as hex text ("\x0301...").
 */
static int
hex_digit_value(char digit)
{
	if (digit >= '0' && digit <= '9')
		return digit - '0';
	if (digit >= 'a' && digit <= 'f')
		return digit - 'a' + 10;
	if (digit >= 'A' && digit <= 'F')
		return digit - 'A' + 10;
	return -1;
}

/*
 * decode_filter
 *
 * What it does: reads the 24-byte sjbloom header of a filter and
 * describes it, e.g. "mode=bloom keys=95017 m=1471893 k=10
 * bytes_sent=184014".
 *
 * Inputs:  value   - the parameter as sent: hex text ("\x" + hex
 *                    digits), or the raw bytes if binary
 *          length  - number of raw bytes (binary only)
 *          binary  - true if the filter was sent in binary (Batch 7)
 *          runtime - the description is written here
 * Output:  true if the value really is an sjbloom filter
 *
 * Why it exists: EXPLAIN ANALYZE shows what the filter really was, which
 * sjb_build_auto only decided at run time.
 */
static bool
decode_filter(const char *value, int length, bool binary, SemijoinRuntime *runtime)
{
	unsigned char header[SJB_HEADER_SIZE];
	size_t		bytes_sent;
	uint8		version;
	uint8		mode;
	uint16		k;
	uint32		num_keys;
	uint64		m;
	int			i;

	if (binary)
	{
		/* the raw bytes: the header is simply the first 24 of them */
		if (length < SJB_HEADER_SIZE)
			return false;
		memcpy(header, value, SJB_HEADER_SIZE);
		bytes_sent = length;
	}
	else
	{
		/* hex text: two hex digits per byte, after "\x" */
		bytes_sent = strlen(value);
		if (bytes_sent < 2 + 2 * SJB_HEADER_SIZE || value[0] != '\\' || value[1] != 'x')
			return false;

		for (i = 0; i < SJB_HEADER_SIZE; i++)
		{
			int			high = hex_digit_value(value[2 + 2 * i]);
			int			low = hex_digit_value(value[2 + 2 * i + 1]);

			if (high < 0 || low < 0)
				return false;
			header[i] = (unsigned char) (high * 16 + low);
		}
	}

	/* read the fields with memcpy, never by casting pointers */
	memcpy(&version, header + SJB_OFFSET_VERSION, sizeof(version));
	memcpy(&mode, header + SJB_OFFSET_MODE, sizeof(mode));
	memcpy(&k, header + SJB_OFFSET_K, sizeof(k));
	memcpy(&num_keys, header + SJB_OFFSET_NKEYS, sizeof(num_keys));
	memcpy(&m, header + SJB_OFFSET_M, sizeof(m));

	if (version != SJB_HEADER_VERSION)
		return false;

	if (mode == 1)
		snprintf(runtime->description, sizeof(runtime->description),
				 "mode=bloom keys=%u m=%llu k=%u bytes_sent=%zu%s",
				 (unsigned int) num_keys, (unsigned long long) m,
				 (unsigned int) k, bytes_sent, binary ? " (binary)" : "");
	else if (mode == 2)
		snprintf(runtime->description, sizeof(runtime->description),
				 "mode=exact keys=%u bytes_sent=%zu%s",
				 (unsigned int) num_keys, bytes_sent, binary ? " (binary)" : "");
	else if (mode == 3)
		snprintf(runtime->description, sizeof(runtime->description),
				 "mode=pass bytes_sent=%zu%s", bytes_sent, binary ? " (binary)" : "");
	else
		return false;
	return true;
}

/*
 * decode_key_list_text
 *
 * What it does: counts the elements of an int4[] in text form, e.g.
 * "{12,345,6789}" has 3, and describes it: "3 bytes_sent=13".
 *
 * Inputs:  value - the parameter as sent; runtime - written here
 * Output:  true if the text looks like an array
 *
 * Why it exists: EXPLAIN ANALYZE shows how many keys the index path sent.
 */
static bool
decode_key_list_text(const char *value, SemijoinRuntime *runtime)
{
	size_t		length = strlen(value);
	long		num_keys = 0;
	size_t		i;

	if (length < 2 || value[0] != '{' || value[length - 1] != '}')
		return false;

	if (length > 2)
	{
		num_keys = 1;			/* n elements are separated by n - 1 commas */
		for (i = 1; i < length - 1; i++)
		{
			if (value[i] == ',')
				num_keys++;
		}
	}

	snprintf(runtime->description, sizeof(runtime->description),
			 "%ld bytes_sent=%zu", num_keys, length);
	return true;
}

/*
 * pgfdw_semijoin_decode_param
 *
 * What it does: called by create_cursor with the value of our parameter,
 * just before it is sent; describes it for EXPLAIN ANALYZE.
 *
 * Inputs:  value   - the parameter's text, or its raw bytes if binary
 *                    (NULL if the value is NULL)
 *          length  - number of raw bytes (binary only, else -1)
 *          binary  - true if sent in binary (semijoin_binary_filter)
 *          path    - SEMIJOIN_PATH_INDEX or SEMIJOIN_PATH_FILTER
 *          runtime - filled in; runtime->decoded = false if the value
 *                    could not be read ("unavailable")
 * Output:  none. It never raises an error.
 *
 * Why it exists: to show what really happened at run time.
 */
void
pgfdw_semijoin_decode_param(const char *value, int length, bool binary,
							int path, SemijoinRuntime *runtime)
{
	runtime->decoded = false;
	if (value == NULL)
		return;

	if (path == SEMIJOIN_PATH_FILTER)
		runtime->decoded = decode_filter(value, length, binary, runtime);
	else if (!binary)
		runtime->decoded = decode_key_list_text(value, runtime);
}

/*
 * pgfdw_semijoin_explain
 *
 * What it does: adds our lines to EXPLAIN of a rewritten foreign scan:
 *     Semijoin Path: index | filter
 *     Semijoin Estimated Keys: <n_est>
 *     Semijoin Predicted Time: index=<ms> filter=<ms>
 * and with ANALYZE what was really sent:
 *     Semijoin Filter: mode=... keys=... m=... k=... bytes_sent=...
 *     Semijoin Keys Sent: <number of keys> bytes_sent=...
 *
 * Inputs:  info    - the List made by pgfdw_semijoin_plan_info
 *          runtime - filled in by create_cursor, or NULL (plain EXPLAIN)
 *          es      - EXPLAIN's state
 * Output:  none
 *
 * Why it exists: so a user can see in EXPLAIN what our hook decided.
 */
void
pgfdw_semijoin_explain(List *info, SemijoinRuntime *runtime, ExplainState *es)
{
	int			path = intVal(list_nth(info, SemijoinPrivatePath));
	double		n_est = floatVal(list_nth(info, SemijoinPrivateKeys));
	double		index_ms = floatVal(list_nth(info, SemijoinPrivateIndexMs));
	double		filter_ms = floatVal(list_nth(info, SemijoinPrivateFilterMs));
	const char *runtime_text = "unavailable";

	/* ExplainPropertyText / ...Float add one "Label: value" line */
	ExplainPropertyText("Semijoin Path",
						path == SEMIJOIN_PATH_INDEX ? "index" : "filter", es);
	ExplainPropertyFloat("Semijoin Estimated Keys", NULL, n_est, 0, es);
	ExplainPropertyText("Semijoin Predicted Time",
						psprintf("index=%.3f ms filter=%.3f ms", index_ms, filter_ms),
						es);

	if (!es->analyze)
		return;

	if (runtime != NULL && runtime->decoded)
		runtime_text = runtime->description;
	ExplainPropertyText(path == SEMIJOIN_PATH_FILTER ? "Semijoin Filter" : "Semijoin Keys Sent",
						runtime_text, es);
}

