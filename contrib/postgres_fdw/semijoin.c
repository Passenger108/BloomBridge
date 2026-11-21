#include "postgres.h"

#include <math.h>

#include "access/htup_details.h"
#include "access/sysattr.h"
#include "access/xact.h"
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

#define SJB_INT4_TEXT_WIDTH 7

#define SJB_ROW_OVERHEAD_BYTES 7
#define SJB_COLUMN_OVERHEAD_BYTES 4

#define SJB_DEFAULT_FETCH_SIZE 100

planner_hook_type prev_planner_hook = NULL;

static bool in_semijoin_hook = false;

typedef struct SjbCandidate
{
	Index		local_varno;
	Oid			local_relid;
	AttrNumber	local_attno;
	char	   *local_alias;
	bool		local_inh;

	Index		foreign_varno;
	Oid			foreign_relid;
	AttrNumber	foreign_attno;
	Var		   *foreign_var;

	List	   *local_quals;

	Oid			sjbloom_oid;
	char	   *sjbloom_schema;

	const char *reject_reason;

	bool		always_report;

	bool		uses_foreign_table;
} SjbCandidate;

typedef struct SjbStats
{
	double		s_rows;
	double		d_remote;
	double		rows_per_key;
	double		row_width;
	int			num_columns;
	int			fetch_size;
	double		r_local;
	double		n_local;
	double		d_local;
	double		n_est;
} SjbStats;

typedef struct TableRefs
{
	Index		local_varno;
	Index		foreign_varno;
	bool		uses_local;
	bool		uses_foreign;
	bool		uses_other;
} TableRefs;

static void
split_and_clauses(Node *node, List **clauses)
{
	if (node == NULL)
		return;

	if (IsA(node, BoolExpr) && ((BoolExpr *) node)->boolop == AND_EXPR)
	{
		BoolExpr   *and_expr = (BoolExpr *) node;
		ListCell   *cell;

		foreach(cell, and_expr->args)
			split_and_clauses((Node *) lfirst(cell), clauses);
		return;
	}

	*clauses = lappend(*clauses, node);
}

static bool
collect_join_tree_quals(Node *node, List **clauses)
{
	ListCell   *cell;

	if (node == NULL)
		return true;

	if (IsA(node, RangeTblRef))
		return true;

	if (IsA(node, FromExpr))
	{
		FromExpr   *from = (FromExpr *) node;

		foreach(cell, from->fromlist)
		{
			if (!collect_join_tree_quals((Node *) lfirst(cell), clauses))
				return false;
		}
		split_and_clauses(from->quals, clauses);
		return true;
	}

	if (IsA(node, JoinExpr))
	{
		JoinExpr   *join = (JoinExpr *) node;

		if (join->jointype != JOIN_INNER)
			return false;
		if (!collect_join_tree_quals(join->larg, clauses))
			return false;
		if (!collect_join_tree_quals(join->rarg, clauses))
			return false;
		split_and_clauses(join->quals, clauses);
		return true;
	}

	return false;
}

static bool
table_refs_walker(Node *node, TableRefs *refs)
{
	if (node == NULL)
		return false;

	if (IsA(node, Var))
	{
		Var		   *var = (Var *) node;

		if (var->varlevelsup != 0)
			refs->uses_other = true;
		else if (var->varno == refs->local_varno)
			refs->uses_local = true;
		else if (var->varno == refs->foreign_varno)
			refs->uses_foreign = true;
		else
			refs->uses_other = true;
		return false;
	}

	return expression_tree_walker(node, table_refs_walker, refs);
}

static bool
contains_param_walker(Node *node, void *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, Param))
		return true;
	return expression_tree_walker(node, contains_param_walker, context);
}

static bool
contains_sjb_contains_walker(Node *node, void *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, FuncExpr))
	{
		FuncExpr   *func = (FuncExpr *) node;
		char	   *name = get_func_name(func->funcid);

		if (name != NULL && strcmp(name, "sjb_contains") == 0)
			return true;
	}
	return expression_tree_walker(node, contains_sjb_contains_walker, context);
}

static bool
is_join_clause(Node *clause, SjbCandidate *c, Var **local_var, Var **foreign_var)
{
	OpExpr	   *op = (OpExpr *) clause;
	Var		   *left;
	Var		   *right;

	if (!IsA(clause, OpExpr) || op->opno != Int4EqualOperator ||
		list_length(op->args) != 2 ||
		!IsA(linitial(op->args), Var) || !IsA(lsecond(op->args), Var))
		return false;

	left = linitial_node(Var, op->args);
	right = lsecond_node(Var, op->args);
	if (left->varlevelsup != 0 || right->varlevelsup != 0)
		return false;

	if (left->varno == c->foreign_varno)
	{
		Var		   *tmp = left;

		left = right;
		right = tmp;
	}

	if (left->varno != c->local_varno || right->varno != c->foreign_varno)
		return false;

	*local_var = left;
	*foreign_var = right;
	return true;
}

static DefElem *
find_option(List *options, const char *name)
{
	ListCell   *cell;

	foreach(cell, options)
	{
		DefElem    *def = (DefElem *) lfirst(cell);

		if (strcmp(def->defname, name) == 0)
			return def;
	}
	return NULL;
}

static bool
find_tables(Query *q, SjbCandidate *c)
{
	ListCell   *cell;
	int			num_relations = 0;
	Index		rt_index = 0;

	foreach(cell, q->rtable)
	{
		RangeTblEntry *rte = (RangeTblEntry *) lfirst(cell);

		rt_index++;

		if (rte->rtekind == RTE_JOIN || rte->rtekind == RTE_GROUP)
			continue;
		if (rte->rtekind != RTE_RELATION)
		{
			c->reject_reason = "the query uses something other than tables (subquery, function, ...)";
			return false;
		}

		num_relations++;
		if (rte->relkind == RELKIND_FOREIGN_TABLE)
		{
			c->foreign_varno = rt_index;
			c->foreign_relid = rte->relid;
		}
		else if (rte->relkind == RELKIND_RELATION)
		{
			if (rte->securityQuals != NIL || rte->tablesample != NULL)
			{
				c->reject_reason = "the local table has row-level security or TABLESAMPLE";
				return false;
			}
			c->local_varno = rt_index;
			c->local_relid = rte->relid;
			c->local_alias = rte->eref->aliasname;
			c->local_inh = rte->inh;
		}
	}

	if (num_relations != 2 || c->local_varno == 0 || c->foreign_varno == 0)
	{
		c->reject_reason = "the query does not join exactly one local table with one foreign table";
		return false;
	}
	return true;
}

static bool
server_allows_semijoin(SjbCandidate *c)
{
	ForeignTable *table = GetForeignTable(c->foreign_relid);
	ForeignServer *server = GetForeignServer(table->serverid);
	ForeignDataWrapper *wrapper = GetForeignDataWrapper(server->fdwid);
	char	   *handler_name = get_func_name(wrapper->fdwhandler);
	DefElem    *filter_opt;
	DefElem    *extensions_opt;
	bool		sjbloom_listed = false;

	if (handler_name == NULL || strcmp(handler_name, "postgres_fdw_handler") != 0)
	{
		c->reject_reason = "the foreign table does not use postgres_fdw";
		return false;
	}

	filter_opt = find_option(table->options, "semijoin_filter");
	if (filter_opt == NULL)
		filter_opt = find_option(server->options, "semijoin_filter");

	extensions_opt = find_option(server->options, "extensions");
	if (extensions_opt != NULL)
		sjbloom_listed = list_member_oid(ExtractExtensionList(defGetString(extensions_opt), false),
										 c->sjbloom_oid);

	if (filter_opt == NULL || !defGetBoolean(filter_opt))
	{
		c->reject_reason = "semijoin_filter is not true for this server/table";
		return false;
	}
	if (!sjbloom_listed)
	{
		c->reject_reason = "the server's \"extensions\" option does not list sjbloom";
		return false;
	}
	return true;
}

static bool
check_conditions(Query *q, SjbCandidate *c)
{
	List	   *clauses = NIL;
	ListCell   *cell;
	int			num_join_clauses = 0;

	if (!collect_join_tree_quals((Node *) q->jointree, &clauses))
	{
		c->reject_reason = "the query uses a join that is not an INNER JOIN";
		return false;
	}

	foreach(cell, clauses)
	{
		Node	   *clause = (Node *) lfirst(cell);
		Var		   *local_var;
		Var		   *foreign_var;
		TableRefs	refs;

		if (contains_sjb_contains_walker(clause, NULL))
		{
			c->reject_reason = "the query already uses sjb_contains";
			return false;
		}

		if (is_join_clause(clause, c, &local_var, &foreign_var))
		{
			num_join_clauses++;
			c->local_attno = local_var->varattno;
			c->foreign_attno = foreign_var->varattno;
			c->foreign_var = foreign_var;
			continue;
		}

		if (checkExprHasSubLink(clause))
		{
			c->reject_reason = "a condition contains a subquery";
			return false;
		}

		memset(&refs, 0, sizeof(refs));
		refs.local_varno = c->local_varno;
		refs.foreign_varno = c->foreign_varno;
		table_refs_walker(clause, &refs);

		if (refs.uses_other || (refs.uses_local && refs.uses_foreign))
		{
			c->reject_reason = "another condition uses both tables";
			return false;
		}
		if (refs.uses_foreign)
			continue;

		if (contain_volatile_functions(clause))
		{
			c->reject_reason = "a local condition contains a volatile function";
			return false;
		}
		if (contains_param_walker(clause, NULL))
		{
			c->reject_reason = "a local condition contains a parameter ($n)";
			return false;
		}
		c->local_quals = lappend(c->local_quals, clause);
	}

	if (num_join_clauses != 1)
	{
		c->reject_reason = "there is not exactly one \"local int4 = foreign int4\" join condition";
		return false;
	}
	return true;
}

static bool
query_uses_foreign_table(Query *q)
{
	ListCell   *cell;

	foreach(cell, q->rtable)
	{
		RangeTblEntry *rte = (RangeTblEntry *) lfirst(cell);

		if (rte->rtekind == RTE_RELATION && rte->relkind == RELKIND_FOREIGN_TABLE)
			return true;
	}
	return false;
}

static bool
find_candidate(Query *q, SjbCandidate *c)
{
	memset(c, 0, sizeof(SjbCandidate));
	c->uses_foreign_table = query_uses_foreign_table(q);

	if (!c->uses_foreign_table)
	{
		c->reject_reason = "the query uses no foreign table";
		return false;
	}

	if (q->commandType != CMD_SELECT || q->utilityStmt != NULL ||
		q->setOperations != NULL || q->rowMarks != NIL || q->hasModifyingCTE)
	{
		c->reject_reason = "the query is not a plain SELECT";
		return false;
	}

	if (!find_tables(q, c))
		return false;

	c->sjbloom_oid = get_extension_oid("sjbloom", true);
	if (!OidIsValid(c->sjbloom_oid))
	{
		c->reject_reason = "the sjbloom extension is not installed here";
		return false;
	}

	if (!server_allows_semijoin(c))
		return false;

	if (!check_conditions(q, c))
		return false;

	return true;
}

static double
get_reltuples(Oid relid)
{
	HeapTuple	tuple;
	double		reltuples;

	tuple = SearchSysCache1(RELOID, ObjectIdGetDatum(relid));
	if (!HeapTupleIsValid(tuple))
		return -1;
	reltuples = ((Form_pg_class) GETSTRUCT(tuple))->reltuples;
	ReleaseSysCache(tuple);
	return reltuples;
}

static double
get_n_distinct(Oid relid, AttrNumber attno, double reltuples)
{
	HeapTuple	tuple;
	double		stadistinct;
	double		n_distinct;

	tuple = SearchSysCache3(STATRELATTINH,
							ObjectIdGetDatum(relid),
							Int16GetDatum(attno),
							BoolGetDatum(false));
	if (!HeapTupleIsValid(tuple))
		return 0;
	stadistinct = ((Form_pg_statistic) GETSTRUCT(tuple))->stadistinct;
	ReleaseSysCache(tuple);

	if (stadistinct == 0)
		return 0;

	n_distinct = stadistinct > 0 ? stadistinct : -stadistinct * reltuples;
	return Max(n_distinct, 1);
}

static double
column_text_width(Oid relid, AttrNumber attno)
{
	Oid			type_id;
	int32		typmod;
	Oid			collation;
	int32		width;

	get_atttypetypmodcoll(relid, attno, &type_id, &typmod, &collation);
	if (type_id == INT4OID)
		return SJB_INT4_TEXT_WIDTH;

	width = get_attavgwidth(relid, attno);
	if (width <= 0)
		width = get_typavgwidth(type_id, typmod);
	return width;
}

static Bitmapset *
foreign_columns_used(Query *q, SjbCandidate *c)
{
	Bitmapset  *columns = NULL;
	ListCell   *cell;

	pull_varattnos((Node *) q->targetList, c->foreign_varno, &columns);
	pull_varattnos((Node *) q->jointree, c->foreign_varno, &columns);
	pull_varattnos(q->havingQual, c->foreign_varno, &columns);

	foreach(cell, q->rtable)
	{
		RangeTblEntry *rte = (RangeTblEntry *) lfirst(cell);

		if (rte->rtekind == RTE_GROUP)
			pull_varattnos((Node *) rte->groupexprs, c->foreign_varno, &columns);
	}

	columns = bms_add_member(columns,
							 c->foreign_attno - FirstLowInvalidHeapAttributeNumber);
	return columns;
}

static int
get_fetch_size(SjbCandidate *c)
{
	ForeignTable *table = GetForeignTable(c->foreign_relid);
	ForeignServer *server = GetForeignServer(table->serverid);
	List	   *option_lists[2] = {server->options, table->options};
	int			fetch_size = SJB_DEFAULT_FETCH_SIZE;

	for (int i = 0; i < 2; i++)
	{
		DefElem    *def = find_option(option_lists[i], "fetch_size");
		int			value;

		if (def != NULL && parse_int(defGetString(def), &value, 0, NULL) && value > 0)
			fetch_size = value;
	}
	return fetch_size;
}

static bool
collect_remote_stats(Query *q, SjbCandidate *c, SjbStats *stats)
{
	Bitmapset  *columns;
	int			member;
	double		text_width = 0;

	stats->s_rows = get_reltuples(c->foreign_relid);
	if (stats->s_rows < 0)
	{
		c->reject_reason = psprintf("the foreign table has no statistics: run ANALYZE %s at site_a",
									get_rel_name(c->foreign_relid));
		c->always_report = true;
		return false;
	}
	if (stats->s_rows == 0)
	{
		c->reject_reason = "the foreign table is empty";
		return false;
	}

	stats->d_remote = get_n_distinct(c->foreign_relid, c->foreign_attno, stats->s_rows);
	if (stats->d_remote <= 0)
	{
		c->reject_reason = psprintf("the foreign join column has no statistics: run ANALYZE %s at site_a",
									get_rel_name(c->foreign_relid));
		c->always_report = true;
		return false;
	}
	stats->rows_per_key = stats->s_rows / stats->d_remote;

	columns = foreign_columns_used(q, c);
	stats->num_columns = 0;
	member = -1;
	while ((member = bms_next_member(columns, member)) >= 0)
	{
		AttrNumber	attno = member + FirstLowInvalidHeapAttributeNumber;

		if (attno <= 0)
		{
			c->reject_reason = "the query uses a system column or a whole-row reference of the foreign table";
			return false;
		}
		text_width += column_text_width(c->foreign_relid, attno);
		stats->num_columns++;
	}
	stats->row_width = text_width + SJB_ROW_OVERHEAD_BYTES +
		SJB_COLUMN_OVERHEAD_BYTES * stats->num_columns;

	stats->fetch_size = get_fetch_size(c);
	return true;
}

static char *
local_key_text(SjbCandidate *c)
{
	return psprintf("%s.%s",
					quote_identifier(c->local_alias),
					quote_identifier(get_attname(c->local_relid, c->local_attno, false)));
}

static char *
build_local_select(SjbCandidate *c, const char *select_list)
{
	StringInfoData sql;
	List	   *deparse_context;
	char	   *alias = (char *) quote_identifier(c->local_alias);
	char	   *table_name;
	ListCell   *cell;

	table_name = quote_qualified_identifier(get_namespace_name(get_rel_namespace(c->local_relid)),
											get_rel_name(c->local_relid));

	initStringInfo(&sql);
	appendStringInfo(&sql, "SELECT %s FROM %s%s %s WHERE %s IS NOT NULL",
					 select_list,
					 c->local_inh ? "" : "ONLY ",
					 table_name,
					 alias,
					 local_key_text(c));

	deparse_context = deparse_context_for(c->local_alias, c->local_relid);
	foreach(cell, c->local_quals)
	{
		Node	   *qual = copyObject((Node *) lfirst(cell));

		ChangeVarNodes(qual, c->local_varno, 1, 0);
		appendStringInfo(&sql, " AND (%s)",
						 deparse_expression(qual, deparse_context, true, false));
	}
	return sql.data;
}

static Query *
parse_select(const char *sql)
{
	List	   *raw_statements;

	raw_statements = raw_parser(sql, RAW_PARSE_DEFAULT);
	if (list_length(raw_statements) != 1)
		elog(ERROR, "semijoin: expected one statement in: %s", sql);

	return parse_analyze_fixedparams(linitial_node(RawStmt, raw_statements),
									 sql, NULL, 0, NULL);
}

static void
estimate_local_keys(SjbCandidate *c, SjbStats *stats)
{
	char	   *sql = build_local_select(c, local_key_text(c));
	Query	   *query = parse_select(sql);
	PlannedStmt *plan;

	plan = standard_planner(query, sql, 0, NULL);
	stats->r_local = plan->planTree->plan_rows;

	stats->n_local = get_reltuples(c->local_relid);
	stats->d_local = get_n_distinct(c->local_relid, c->local_attno,
									stats->n_local);
	if (stats->n_local <= 0 || stats->d_local <= 0)
	{
		stats->n_est = stats->r_local;
		return;
	}

	stats->d_local = Min(stats->d_local, stats->n_local);
	stats->n_est = stats->d_local;

	if (stats->r_local < stats->n_local)
		stats->n_est *= 1.0 - pow((stats->n_local - stats->r_local) / stats->n_local,
								  stats->n_local / stats->d_local);

	stats->n_est = Max(stats->n_est, 1);
}

static Node *
make_expr_sublink(Query *subquery)
{
	SubLink    *sublink = makeNode(SubLink);

	sublink->subLinkType = EXPR_SUBLINK;
	sublink->subselect = (Node *) subquery;
	sublink->location = -1;
	return (Node *) sublink;
}

static Node *
build_index_condition(SjbCandidate *c, char **sql)
{
	ScalarArrayOpExpr *any_expr = makeNode(ScalarArrayOpExpr);
	Node *sublink;

	*sql = build_local_select(c, psprintf("array_agg(DISTINCT %s)", local_key_text(c)));
	sublink = make_expr_sublink(parse_select(*sql));

	any_expr->opno = Int4EqualOperator;
	any_expr->opfuncid = get_opcode(Int4EqualOperator);
	any_expr->useOr = true;
	any_expr->args = list_make2(copyObject(c->foreign_var), sublink);
	any_expr->location = -1;
	return (Node *) any_expr;
}

static void
report_rewrite(SjbStats *stats, const char *sql)
{
	ereport(NOTICE,
			(errmsg("postgres_fdw semijoin: index path: n_est=%.1f (r=%.0f, N=%.0f, D_local=%.0f), s_rows=%.0f, rows_per_key=%.3f, row_width=%.2f (%d columns), fetch_size=%d",
					stats->n_est, stats->r_local, stats->n_local, stats->d_local,
					stats->s_rows, stats->rows_per_key, stats->row_width,
					stats->num_columns, stats->fetch_size),
			 errdetail("sub-SELECT: %s", sql)));
}

static Node *
plan_semijoin(Query *q, SjbCandidate *c)
{
	SjbStats	stats;
	Node	   *condition;
	char	   *sql = NULL;

	memset(&stats, 0, sizeof(stats));
	c->sjbloom_schema = get_namespace_name(get_extension_schema(c->sjbloom_oid));
	if (c->sjbloom_schema == NULL)
	{
		c->reject_reason = "the schema of sjbloom was not found";
		return NULL;
	}

	if (!collect_remote_stats(q, c, &stats))
		return NULL;
	estimate_local_keys(c, &stats);

	condition = build_index_condition(c, &sql);

	if (pgfdw_semijoin_verbose)
		report_rewrite(&stats, sql);
	return condition;
}

static Node *
try_plan_semijoin(Query *q, SjbCandidate *c)
{
	MemoryContext old_context = CurrentMemoryContext;
	ResourceOwner old_owner = CurrentResourceOwner;
	Node	   *condition = NULL;

	BeginInternalSubTransaction(NULL);
	MemoryContextSwitchTo(old_context);

	PG_TRY();
	{
		condition = plan_semijoin(q, c);

		ReleaseCurrentSubTransaction();
		MemoryContextSwitchTo(old_context);
		CurrentResourceOwner = old_owner;
	}
	PG_CATCH();
	{
		ErrorData  *error;

		MemoryContextSwitchTo(old_context);
		error = CopyErrorData();
		FlushErrorState();
		RollbackAndReleaseCurrentSubTransaction();
		MemoryContextSwitchTo(old_context);
		CurrentResourceOwner = old_owner;

		if (error->sqlerrcode == ERRCODE_QUERY_CANCELED)
			ReThrowError(error);

		condition = NULL;
		c->reject_reason = psprintf("internal problem, query left unchanged: %s",
									error->message);
		c->always_report = true;
		FreeErrorData(error);
	}
	PG_END_TRY();

	return condition;
}

static void
attach_condition(Query *q, Node *condition)
{
	Node *new_quals = make_and_qual(q->jointree->quals, condition);

	q->jointree->quals = new_quals;
	q->hasSubLinks = true;
}

PlannedStmt *
pgfdw_semijoin_planner(Query *parse, const char *query_string,
					   int cursorOptions, ParamListInfo boundParams)
{
	if (pgfdw_enable_semijoin && !in_semijoin_hook && !IsInParallelMode())
	{
		SjbCandidate candidate;
		Node	   *condition = NULL;

		in_semijoin_hook = true;
		PG_TRY();
		{
			if (find_candidate(parse, &candidate))
				condition = try_plan_semijoin(parse, &candidate);

			if (condition != NULL)
				attach_condition(parse, condition);
			else if (candidate.uses_foreign_table &&
					 (pgfdw_semijoin_verbose || candidate.always_report))
				ereport(NOTICE,
						(errmsg("postgres_fdw semijoin: no rewrite: %s",
								candidate.reject_reason)));
		}
		PG_FINALLY();
		{
			in_semijoin_hook = false;
		}
		PG_END_TRY();
	}

	if (prev_planner_hook != NULL)
		return prev_planner_hook(parse, query_string, cursorOptions, boundParams);
	return standard_planner(parse, query_string, cursorOptions, boundParams);
}
