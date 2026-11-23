#ifndef POSTGRES_FDW_H
#define POSTGRES_FDW_H

#include "foreign/foreign.h"
#include "lib/stringinfo.h"
#include "libpq-fe.h"
#include "nodes/execnodes.h"
#include "nodes/pathnodes.h"
#include "optimizer/planner.h"
#include "utils/relcache.h"


typedef struct PgFdwRelationInfo
{

	bool		pushdown_safe;
	List	   *remote_conds;
	List	   *local_conds;
	List	   *final_remote_exprs;
	Bitmapset  *attrs_used;
	bool		qp_is_pushdown_safe;
	QualCost	local_conds_cost;
	Selectivity local_conds_sel;
	Selectivity joinclause_sel;
	double		rows;
	int			width;
	int			disabled_nodes;
	Cost		startup_cost;
	Cost		total_cost;
	double		retrieved_rows;
	Cost		rel_startup_cost;
	Cost		rel_total_cost;
	bool		use_remote_estimate;
	Cost		fdw_startup_cost;
	Cost		fdw_tuple_cost;
	List	   *shippable_extensions;
	bool		async_capable;
	ForeignTable *table;
	ForeignServer *server;
	UserMapping *user;			
	int			fetch_size;	
	char	   *relation_name;
	RelOptInfo *outerrel;
	RelOptInfo *innerrel;
	JoinType	jointype;
	List	   *joinclauses;	

	UpperRelationKind stage;

	List	   *grouped_tlist;


	bool		make_outerrel_subquery; 
	bool		make_innerrel_subquery; 
	Relids		lower_subquery_rels;	
	Relids		hidden_subquery_rels;	

	int			relation_index;
} PgFdwRelationInfo;



typedef struct PgFdwConnState
{
	AsyncRequest *pendingAreq;
} PgFdwConnState;



typedef enum PgFdwSamplingMethod
{
	ANALYZE_SAMPLE_OFF,			
	ANALYZE_SAMPLE_AUTO,		
	ANALYZE_SAMPLE_RANDOM,		
	ANALYZE_SAMPLE_SYSTEM,		
	ANALYZE_SAMPLE_BERNOULLI,	
} PgFdwSamplingMethod;


extern int	set_transmission_modes(void);
extern void reset_transmission_modes(int nestlevel);
extern void process_pending_request(AsyncRequest *areq);


extern PGconn *GetConnection(UserMapping *user, bool will_prep_stmt, PgFdwConnState **state);
extern void ReleaseConnection(PGconn *conn);
extern unsigned int GetCursorNumber(PGconn *conn);
extern unsigned int GetPrepStmtNumber(PGconn *conn);
extern void do_sql_command(PGconn *conn, const char *sql);
extern PGresult *pgfdw_get_result(PGconn *conn);
extern PGresult *pgfdw_exec_query(PGconn *conn, const char *query, PgFdwConnState *state);
extern void pgfdw_report_error(int elevel, PGresult *res, PGconn *conn, bool clear, const char *sql);


extern int	ExtractConnectionOptions(List *defelems,
									 const char **keywords,
									 const char **values);
extern List *ExtractExtensionList(const char *extensionsString, bool warnOnMissing);
extern char *process_pgfdw_appname(const char *appname);
extern char *pgfdw_application_name;


#define SEMIJOIN_PATH_AUTO		0	
#define SEMIJOIN_PATH_INDEX		1	
#define SEMIJOIN_PATH_FILTER	2	

extern bool pgfdw_enable_semijoin;
extern int	pgfdw_semijoin_force_path;
extern bool pgfdw_semijoin_verbose;
extern bool pgfdw_semijoin_binary_filter;
extern double pgfdw_semijoin_network_mbit;
extern int	pgfdw_semijoin_max_filter_kb;
extern double pgfdw_semijoin_t_check_ns;
extern double pgfdw_semijoin_t_lookup_us;
extern double pgfdw_semijoin_per_message_ms;
extern double pgfdw_semijoin_per_row_us;
extern double pgfdw_semijoin_t_build_us;


extern void classifyConditions(PlannerInfo *root,
							   RelOptInfo *baserel,
							   List *input_conds,
							   List **remote_conds,
							   List **local_conds);

							
extern bool is_foreign_expr(PlannerInfo *root,
							RelOptInfo *baserel,
							Expr *expr);

extern bool is_foreign_param(PlannerInfo *root,
							 RelOptInfo *baserel,
							 Expr *expr);


extern bool is_foreign_pathkey(PlannerInfo *root,
							   RelOptInfo *baserel,
							   PathKey *pathkey);

extern void deparseInsertSql(StringInfo buf, RangeTblEntry *rte,
							 Index rtindex, Relation rel,
							 List *targetAttrs, bool doNothing,
							 List *withCheckOptionList, List *returningList,
							 List **retrieved_attrs, int *values_end_len);


extern void rebuildInsertSql(StringInfo buf, Relation rel,
							 char *orig_query, List *target_attrs,
							 int values_end_len, int num_params,
							 int num_rows);


extern void deparseUpdateSql(StringInfo buf, RangeTblEntry *rte,
							 Index rtindex, Relation rel,
							 List *targetAttrs,
							 List *withCheckOptionList, List *returningList,
							 List **retrieved_attrs);

							 
extern void deparseDirectUpdateSql(StringInfo buf, PlannerInfo *root,
								   Index rtindex, Relation rel,
								   RelOptInfo *foreignrel,
								   List *targetlist,
								   List *targetAttrs,
								   List *remote_conds,
								   List **params_list,
								   List *returningList,
								   List **retrieved_attrs);


extern void deparseDeleteSql(StringInfo buf, RangeTblEntry *rte,
							 Index rtindex, Relation rel,
							 List *returningList,
							 List **retrieved_attrs);

extern void deparseDirectDeleteSql(StringInfo buf, PlannerInfo *root,
								   Index rtindex, Relation rel,
								   RelOptInfo *foreignrel,
								   List *remote_conds,
								   List **params_list,
								   List *returningList,
								   List **retrieved_attrs);

extern void deparseAnalyzeSizeSql(StringInfo buf, Relation rel);
extern void deparseAnalyzeInfoSql(StringInfo buf, Relation rel);
extern void deparseAnalyzeSql(StringInfo buf, Relation rel,
							  PgFdwSamplingMethod sample_method,
							  double sample_frac,
							  List **retrieved_attrs);

extern void deparseTruncateSql(StringInfo buf, List *rels, DropBehavior behavior, bool restart_seqs);
extern void deparseStringLiteral(StringInfo buf, const char *val);
extern EquivalenceMember *find_em_for_rel(PlannerInfo *root,
										  EquivalenceClass *ec,
										  RelOptInfo *rel);

extern EquivalenceMember *find_em_for_rel_target(PlannerInfo *root,
												 EquivalenceClass *ec,
												 RelOptInfo *rel);

extern List *build_tlist_to_deparse(RelOptInfo *foreignrel);
extern void deparseSelectStmtForRel(StringInfo buf, PlannerInfo *root,
									RelOptInfo *rel, List *tlist,
									List *remote_conds, List *pathkeys,
									bool has_final_sort, bool has_limit,
									bool is_subquery,
									List **retrieved_attrs, List **params_list);


extern const char *get_jointype_name(JoinType jointype);


extern planner_hook_type prev_planner_hook;


typedef struct SemijoinHint
{
	Oid			foreign_relid;	
	AttrNumber	foreign_attno;	
	Oid			contains_funcid;	
	int			path;			
	double		expected_rows;	
	double		n_est;			
	double		index_ms;		
	double		filter_ms;		
} SemijoinHint;

extern SemijoinHint *pgfdw_semijoin_hint;
extern void pgfdw_apply_semijoin_hint(PlannerInfo *root, RelOptInfo *baserel, Oid foreigntableid);


typedef struct SemijoinRuntime
{
	bool		decoded;		
	char		description[160];	
} SemijoinRuntime;

struct ExplainState;			

extern List *pgfdw_semijoin_plan_info(PlannerInfo *root, RelOptInfo *foreignrel,
									  List *remote_conds, List *params_list);
extern int	pgfdw_semijoin_info_path(List *info);
extern int	pgfdw_semijoin_info_param_index(List *info);
extern void pgfdw_semijoin_decode_param(const char *value, int length,
										bool binary, int path,
										SemijoinRuntime *runtime);

extern void pgfdw_semijoin_explain(List *info, SemijoinRuntime *runtime,
								   struct ExplainState *es);

extern PlannedStmt *pgfdw_semijoin_planner(Query *parse,
										   const char *query_string,
										   int cursorOptions,
										   ParamListInfo boundParams);


extern bool is_builtin(Oid objectId);
extern bool is_shippable(Oid objectId, Oid classId, PgFdwRelationInfo *fpinfo);

#endif							
