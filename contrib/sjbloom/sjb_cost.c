/*-------------------------------------------------------------------------
 *
 * sjb_cost.c
 *
 * The SQL-callable functions of the sjbloom COST MODEL:
 *
 *   sjb_build_auto(keys int4[], s_rows, rows_per_key, row_width,
 *                  network_mbit, t_check_ns,
 *                  max_filter_bytes, wire_factor,
 *                  per_message_ms, per_row_us, t_build_us,
 *                  fetch_size) RETURNS bytea
 *       Site A: let the cost model pick the mode (BLOOM, EXACT or PASS)
 *       and the Bloom size, then build that filter.
 *   sjb_choice_report(...) RETURNS text
 *       A readable report of the cost model's estimates.
 *   sjb_plan_choice(...) RETURNS text
 *       'index' or 'filter': which path the cost model picks.
 *   sjb_expected_remote_rows(..., path) RETURNS float8
 *       rows site B is expected to send back on that path.
 *   sjb_predicted_ms(..., path) RETURNS float8
 *       predicted total time of that path in ms.
 *
 * This file only turns SQL values into plain C data and back. The
 * formulas themselves are in costmodel.c; the filter builders are in
 * sjbloom.c (declared in sjb_filter.h).
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <math.h>
#include <stdlib.h>

#include "catalog/pg_type.h"
#include "fmgr.h"
#include "lib/stringinfo.h"
#include "utils/array.h"
#include "utils/builtins.h"

#include "sjb_filter.h"
#include "costmodel.h"

/* ------------------------------------------------------------------------
 * Part 1: reading cost model arguments
 * ------------------------------------------------------------------------
 */

/*
 * check_cost_argument
 *
 * What it does: raises an error if a cost model argument is not a normal
 * number, is negative, or is 0 when 0 is not allowed.
 *
 * Inputs:  name         - the argument name, for the error message
 *          value        - its value
 *          zero_allowed - false for values we divide by (network_mbit,
 *                         wire_factor)
 * Output:  none; returns normally only if the value is valid
 *
 * Why it exists: a NaN, an infinity or a negative count would make the
 * estimates meaningless, and a zero bandwidth would divide by zero.
 */
static void
check_cost_argument(const char *name, double value, bool zero_allowed)
{
	bool		is_valid = true;

	if (isnan(value) || isinf(value) || value < 0)
		is_valid = false;
	if (value == 0 && !zero_allowed)
		is_valid = false;

	if (!is_valid)
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("sjbloom: %s must be a number %s 0, got %g",
						name, zero_allowed ? ">=" : ">", value)));
}

/*
 * check_cost_inputs
 *
 * What it does: checks every field of an SjbCostInputs with
 * check_cost_argument.
 * Input:  inputs
 * Output: none; returns normally only if all values are valid
 * Why it exists: all three SQL functions that use the cost model need
 * the same checks.
 */
static void
check_cost_inputs(const SjbCostInputs *inputs)
{
	check_cost_argument("n", inputs->num_keys, true);
	check_cost_argument("s_rows", inputs->s_rows, true);
	check_cost_argument("rows_per_key", inputs->rows_per_key, true);
	check_cost_argument("row_width", inputs->row_width, true);
	check_cost_argument("network_mbit", inputs->network_mbit, false);
	check_cost_argument("t_check_ns", inputs->t_check_ns, true);
	check_cost_argument("t_lookup_us", inputs->t_lookup_us, true);
	check_cost_argument("max_filter_bytes", inputs->max_filter_bytes, true);
	check_cost_argument("wire_factor", inputs->wire_factor, false);
	check_cost_argument("per_message_ms", inputs->per_message_ms, true);
	check_cost_argument("per_row_us", inputs->per_row_us, true);
	check_cost_argument("t_build_us", inputs->t_build_us, true);
	check_cost_argument("fetch_size", inputs->fetch_size, false);
}

/*
 * read_report_arguments
 *
 * What it does: reads the 12 arguments of sjb_choice_report and
 * sjb_plan_choice (n, s_rows, rows_per_key, row_width, network_mbit,
 * t_check_ns, t_lookup_us, per_message_ms, per_row_us, t_build_us,
 * fetch_size, max_filter_bytes) and the wire_factor (Batch 7) into an
 * SjbCostInputs, uses the default key text length, and checks them.
 *
 * Inputs:  fcinfo - the function call info of the SQL function (it holds
 *                   the arguments; the PG_GETARG_ macros read from it)
 *          wire_factor_argument - the argument number of wire_factor: 12
 *                   for sjb_choice_report / sjb_plan_choice, 13 for the
 *                   functions that take a path first
 * Output:  *inputs is filled in
 *
 * Why it exists: both SQL functions take the same arguments, and they
 * must give the cost model exactly the same inputs.
 */
static void
read_report_arguments(FunctionCallInfo fcinfo, SjbCostInputs *inputs,
					  int wire_factor_argument)
{
	/* PG_GETARG_FLOAT8(i) reads argument number i as a C double. */
	inputs->num_keys = PG_GETARG_FLOAT8(0);
	inputs->s_rows = PG_GETARG_FLOAT8(1);
	inputs->rows_per_key = PG_GETARG_FLOAT8(2);
	inputs->row_width = PG_GETARG_FLOAT8(3);
	inputs->network_mbit = PG_GETARG_FLOAT8(4);
	inputs->t_check_ns = PG_GETARG_FLOAT8(5);
	inputs->t_lookup_us = PG_GETARG_FLOAT8(6);
	inputs->per_message_ms = PG_GETARG_FLOAT8(7);
	inputs->per_row_us = PG_GETARG_FLOAT8(8);
	inputs->t_build_us = PG_GETARG_FLOAT8(9);
	inputs->fetch_size = PG_GETARG_INT32(10);

	/*
	 * Batch 6b: the same limit that sjb_build_auto gets, so that the plan
	 * time decision and the run time filter agree (SQL default: 1 MB).
	 */
	inputs->max_filter_bytes = (double) PG_GETARG_INT64(11);
	/*
	 * Batch 7: 2 when postgres_fdw sends the filter as hex text (the
	 * default), 1 when it sends it in binary (semijoin_binary_filter).
	 */
	inputs->wire_factor = PG_GETARG_FLOAT8(wire_factor_argument);
	inputs->key_text_len = SJB_DEFAULT_KEY_TEXT_LEN;

	check_cost_inputs(inputs);
}

/*
 * mode_name
 *
 * What it does: the lower-case name of a filter mode.
 * Input:  mode (SJB_MODE_...)
 * Output: "bloom", "exact" or "pass"
 * Why it exists: for the report text.
 */
static const char *
mode_name(int mode)
{
	if (mode == SJB_MODE_BLOOM)
		return "bloom";
	if (mode == SJB_MODE_EXACT)
		return "exact";
	return "pass";
}

/*
 * append_estimate_line
 *
 * What it does: appends one line of the report table for one estimate:
 * path, mode, bits/key, bytes A->B, rows back, bytes B->A, messages, then
 * the times in ms: network (bytes / bandwidth), messages, returned rows,
 * work at A, work at B and the total. A skipped mode gets
 * "skipped: <reason>" instead.
 *
 * Inputs:  report   - the text being built
 *          path     - "index" or "filter"
 *          estimate - the estimate to print
 * Output:  none (appends to report)
 *
 * Why it exists: the four lines of the table look the same.
 */
static void
append_estimate_line(StringInfo report, const char *path,
					 const SjbCostEstimate *estimate)
{
	const char *mode_column = "-";
	const char *bits_column = "-";

	if (strcmp(path, "filter") == 0)
		mode_column = estimate->name;

	if (!estimate->allowed)
	{
		/* appendStringInfo adds printf-style text to a StringInfo. */
		appendStringInfo(report, "%-7s %-6s skipped: %s\n",
						 path, mode_column, estimate->skip_reason);
		return;
	}

	if (estimate->bits_per_key > 0)
		bits_column = psprintf("%.2f", estimate->bits_per_key);

	appendStringInfo(report, "%-7s %-6s %8s %12.0f %10.0f %12.0f %8.0f %11.3f %11.3f %9.3f %10.3f %10.3f %11.3f\n",
					 path, mode_column, bits_column,
					 estimate->bytes_a_to_b,
					 estimate->rows_back,
					 estimate->bytes_b_to_a,
					 estimate->messages,
					 estimate->network_seconds * 1000.0,
					 estimate->message_seconds * 1000.0,
					 estimate->row_seconds * 1000.0,
					 estimate->work_at_a_seconds * 1000.0,
					 estimate->work_at_b_seconds * 1000.0,
					 estimate->total_seconds * 1000.0);
}




/* ------------------------------------------------------------------------
 * Part 2: the SQL functions of the cost model
 * ------------------------------------------------------------------------
 */

PG_FUNCTION_INFO_V1(sjb_build_auto);

/*
 * sjb_build_auto(keys int4[], s_rows float8, rows_per_key float8,
 *                row_width float8, network_mbit float8, t_check_ns float8,
 *                max_filter_bytes int8, wire_factor float8,
 *                per_message_ms float8, per_row_us float8,
 *                t_build_us float8, fetch_size int4) RETURNS bytea
 *
 * What it does: builds the filter the cost model says is fastest:
 *   a) collect the non-NULL keys, sort them, remove duplicates -> n
 *   b) n = 0: return an EXACT filter with no keys (nothing passes; the
 *      join is empty, so that is correct)
 *   c) estimate the time of BLOOM (sized with b*), EXACT and PASS, skipping
 *      BLOOM if b* = 0 and any mode whose filter exceeds max_filter_bytes
 *      (sjb_estimate_all in costmodel.c)
 *   d) build the mode with the smallest time; header nkeys = n
 *
 * Inputs:  keys          - site A's join keys (NULLs and repeats allowed)
 *          s_rows        - rows of S at site B (from the catalog)
 *          rows_per_key  - rows of S per key value (from the catalog)
 *          row_width     - bytes per returned row on the wire
 *          network_mbit  - network speed
 *          t_check_ns    - site B's time to scan + check one row
 *          max_filter_bytes - largest BLOOM/EXACT filter allowed
 *          wire_factor   - wire bytes per filter byte (2 = hex text)
 *          per_message_ms, per_row_us, t_build_us - calibrated costs
 *          fetch_size    - rows per postgres_fdw FETCH
 * Output:  the filter (bytea)
 *
 * Why it exists: the filter is chosen at RUNTIME, when the exact number
 * of distinct keys is known, not guessed by the planner.
 */
Datum
sjb_build_auto(PG_FUNCTION_ARGS)
{
	ArrayType  *keys_array = PG_GETARG_ARRAYTYPE_P(0);
	SjbCostInputs inputs;
	SjbChoice	choice;
	int32	   *keys;
	int			num_keys;

	/* Step a: the distinct keys. */
	keys = collect_unique_keys(keys_array, &num_keys);

	/* Read and check the cost model arguments. */
	inputs.num_keys = num_keys;
	inputs.s_rows = PG_GETARG_FLOAT8(1);
	inputs.rows_per_key = PG_GETARG_FLOAT8(2);
	inputs.row_width = PG_GETARG_FLOAT8(3);
	inputs.network_mbit = PG_GETARG_FLOAT8(4);
	inputs.t_check_ns = PG_GETARG_FLOAT8(5);
	inputs.max_filter_bytes = (double) PG_GETARG_INT64(6);
	inputs.wire_factor = PG_GETARG_FLOAT8(7);
	inputs.per_message_ms = PG_GETARG_FLOAT8(8);
	inputs.per_row_us = PG_GETARG_FLOAT8(9);
	inputs.t_build_us = PG_GETARG_FLOAT8(10);
	inputs.fetch_size = PG_GETARG_INT32(11);
	inputs.t_lookup_us = 0.0;	/* only the index path uses it */
	inputs.key_text_len = SJB_DEFAULT_KEY_TEXT_LEN;
	check_cost_inputs(&inputs);

	/* Step b: no keys at all. */
	if (num_keys == 0)
		PG_RETURN_BYTEA_P(build_exact_filter(keys, 0));

	/* Step c: the estimates. */
	sjb_estimate_all(&inputs, &choice);

	/* Step d: build the winner. */
	if (choice.best_filter_mode == SJB_MODE_BLOOM)
		PG_RETURN_BYTEA_P(build_bloom_filter(keys, num_keys,
											 (uint64) choice.bloom.m,
											 (int) choice.bloom.k));

	if (choice.best_filter_mode == SJB_MODE_EXACT)
		PG_RETURN_BYTEA_P(build_exact_filter(keys, num_keys));

	PG_RETURN_BYTEA_P(build_pass_filter(num_keys));
}


PG_FUNCTION_INFO_V1(sjb_choice_report);

/*
 * sjb_choice_report(n, s_rows, rows_per_key, row_width, network_mbit,
 *                   t_check_ns, t_lookup_us, per_message_ms, per_row_us,
 *                   t_build_us float8, fetch_size int4,
 *                   max_filter_bytes int8, wire_factor float8) RETURNS text
 *
 * What it does: runs the cost model (sjb_estimate_all, the same code
 * sjb_build_auto uses) and returns a readable multi-line report: one line
 * for the index path and one for each filter mode, with bytes A->B, rows
 * back, bytes B->A, messages, and the times in ms (network, messages,
 * returned rows, work at A, work at B, total), then the best filter mode
 * and the winner.
 *
 * Inputs:  n            - number of distinct keys at site A
 *          s_rows .. t_check_ns - as for sjb_build_auto
 *          t_lookup_us  - time per key of the index path
 *          per_message_ms .. fetch_size, max_filter_bytes, wire_factor
 *                         - as for sjb_build_auto
 * Output:  the report as text
 *
 * Why it exists: to explain and present the model's decisions, and for
 * bench/validate_model.py to read the predicted times.
 */
Datum
sjb_choice_report(PG_FUNCTION_ARGS)
{
	SjbCostInputs inputs;
	SjbChoice	choice;
	const SjbCostEstimate *best_filter;
	StringInfoData report;

	read_report_arguments(fcinfo, &inputs, 12);
	sjb_estimate_all(&inputs, &choice);
	best_filter = sjb_estimate_for_mode(&choice, choice.best_filter_mode);

	/*
	 * A StringInfo is PostgreSQL's growing text buffer: initStringInfo
	 * starts an empty one, and appendStringInfo adds to the end of it.
	 */
	initStringInfo(&report);
	appendStringInfo(&report,
					 "inputs: n=%.0f s_rows=%.0f rows_per_key=%g row_width=%.2f "
					 "network_mbit=%g t_check_ns=%.2f t_lookup_us=%.4f\n",
					 inputs.num_keys, inputs.s_rows, inputs.rows_per_key,
					 inputs.row_width, inputs.network_mbit,
					 inputs.t_check_ns, inputs.t_lookup_us);
	appendStringInfo(&report,
					 "        per_message_ms=%.4f per_row_us=%.4f t_build_us=%.4f fetch_size=%.0f max_filter_bytes=%.0f\n",
					 inputs.per_message_ms, inputs.per_row_us,
					 inputs.t_build_us, inputs.fetch_size,
					 inputs.max_filter_bytes);
	appendStringInfo(&report, "matching rows M = %.0f\n", choice.matching_rows);
	appendStringInfo(&report, "%-7s %-6s %8s %12s %10s %12s %8s %11s %11s %9s %10s %10s %11s\n",
					 "path", "mode", "bits/key", "bytes_A_to_B", "rows_back",
					 "bytes_B_to_A", "messages", "network_ms", "messages_ms",
					 "rows_ms", "work_A_ms", "work_B_ms", "total_ms");

	append_estimate_line(&report, "index", &choice.index_path);
	append_estimate_line(&report, "filter", &choice.bloom);
	append_estimate_line(&report, "filter", &choice.exact);
	append_estimate_line(&report, "filter", &choice.pass);

	if (choice.bloom.allowed)
		appendStringInfo(&report, "bloom size: m=%.0f bits, k=%.0f, predicted fp rate=%.6f\n",
						 choice.bloom.m, choice.bloom.k, choice.bloom.fp_rate);

	appendStringInfo(&report, "best filter mode: %s (%.3f ms)\n",
					 mode_name(choice.best_filter_mode),
					 best_filter->total_seconds * 1000.0);

	if (choice.index_path_wins)
		appendStringInfo(&report, "winner: index path (%.3f ms <= %.3f ms for filter path with %s)",
						 choice.index_path.total_seconds * 1000.0,
						 best_filter->total_seconds * 1000.0,
						 mode_name(choice.best_filter_mode));
	else
		appendStringInfo(&report, "winner: filter path with %s (%.3f ms < %.3f ms for index path)",
						 mode_name(choice.best_filter_mode),
						 best_filter->total_seconds * 1000.0,
						 choice.index_path.total_seconds * 1000.0);

	PG_RETURN_TEXT_P(cstring_to_text(report.data));
}


PG_FUNCTION_INFO_V1(sjb_plan_choice);

/*
 * sjb_plan_choice(same 13 arguments as sjb_choice_report) RETURNS text
 *
 * What it does: returns 'index' if the index path is estimated to be
 * faster (or equal), otherwise 'filter'.
 *
 * Inputs:  the same as sjb_choice_report
 * Output:  'index' or 'filter'
 *
 * Why it exists: Batch 6's planner hook calls this, so the decision
 * between the two paths lives in ONE place (sjb_estimate_all).
 */
Datum
sjb_plan_choice(PG_FUNCTION_ARGS)
{
	SjbCostInputs inputs;
	SjbChoice	choice;

	read_report_arguments(fcinfo, &inputs, 12);
	sjb_estimate_all(&inputs, &choice);

	if (choice.index_path_wins)
		PG_RETURN_TEXT_P(cstring_to_text("index"));
	PG_RETURN_TEXT_P(cstring_to_text("filter"));
}


/*
 * estimate_for_path
 *
 * What it does: returns the estimate that belongs to a path name:
 *   'index'  - the index path
 *   'filter' - the filter path with the mode the cost model would pick
 *   'auto'   - whichever of the two the cost model picks
 *
 * Inputs:  choice - the result of sjb_estimate_all; path - the path name
 * Output:  a pointer to that estimate (inside *choice); raises an error
 *          for an unknown name
 *
 * Why it exists: sjb_expected_remote_rows and sjb_predicted_ms (Batch 7)
 * both need "the estimate of this path", and it must be found the same
 * way in both.
 */
static const SjbCostEstimate *
estimate_for_path(const SjbChoice *choice, const char *path)
{
	const SjbCostEstimate *best_filter;

	best_filter = sjb_estimate_for_mode(choice, choice->best_filter_mode);

	if (strcmp(path, "index") == 0)
		return &choice->index_path;
	if (strcmp(path, "filter") == 0)
		return best_filter;
	if (strcmp(path, "auto") == 0)
	{
		if (choice->index_path_wins)
			return &choice->index_path;
		return best_filter;
	}

	ereport(ERROR,
			(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
			 errmsg("sjbloom: path must be 'index', 'filter' or 'auto', got '%s'",
					path)));
	return NULL;				/* not reached; keeps the compiler quiet */
}


PG_FUNCTION_INFO_V1(sjb_expected_remote_rows);

/*
 * sjb_expected_remote_rows(the first 12 arguments of sjb_plan_choice,
 *                          path text, wire_factor float8) RETURNS float8
 *
 * What it does: the number of rows site B is expected to send back on
 * the given path: M (the matching rows) on the index path, and on the
 * filter path the rows back of the mode the cost model would pick (for
 * BLOOM: M plus the expected false positives; for PASS: all of S).
 *
 * Inputs:  the 12 cost model arguments; path - 'index', 'filter' or 'auto'
 * Output:  the expected number of rows
 *
 * Why it exists: Batch 7's planner hook gives this number to
 * postgres_fdw's own row estimate, so the planner stops guessing ~10 rows
 * for the rewritten foreign scan. It comes from the same estimate as the
 * path decision (sjb_estimate_all), so the logic lives in one place.
 */
Datum
sjb_expected_remote_rows(PG_FUNCTION_ARGS)
{
	SjbCostInputs inputs;
	SjbChoice	choice;
	char	   *path;

	read_report_arguments(fcinfo, &inputs, 13);
	sjb_estimate_all(&inputs, &choice);

	/* PG_GETARG_TEXT_PP reads a text argument; text_to_cstring makes a C string */
	path = text_to_cstring(PG_GETARG_TEXT_PP(12));
	PG_RETURN_FLOAT8(estimate_for_path(&choice, path)->rows_back);
}


PG_FUNCTION_INFO_V1(sjb_predicted_ms);

/*
 * sjb_predicted_ms(the first 12 arguments of sjb_plan_choice, path text,
 *                  wire_factor float8) RETURNS float8
 *
 * What it does: the predicted total time in ms of the given path (for the
 * filter path: with the mode the cost model would pick). These are the
 * same numbers as the total_ms column of sjb_choice_report.
 *
 * Inputs:  the 12 cost model arguments; path - 'index', 'filter' or 'auto'
 * Output:  the predicted time in milliseconds
 *
 * Why it exists: Batch 7 shows both predicted times in EXPLAIN, and the
 * planner hook should not have to read them out of the report's text.
 */
Datum
sjb_predicted_ms(PG_FUNCTION_ARGS)
{
	SjbCostInputs inputs;
	SjbChoice	choice;
	char	   *path;

	read_report_arguments(fcinfo, &inputs, 13);
	sjb_estimate_all(&inputs, &choice);

	path = text_to_cstring(PG_GETARG_TEXT_PP(12));
	PG_RETURN_FLOAT8(estimate_for_path(&choice, path)->total_seconds * 1000.0);
}

