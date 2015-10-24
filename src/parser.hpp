#ifndef PARSER_H
#define PARSER_H

//#include<algorithm>
//#include "block_information.hpp"
//#include "cgraph_node.hpp"
//#include "dataflow.hpp"
//#include "interval.hpp"
#include<iostream>
#include "gcc-plugin.h"
#include "config.h"
#include "system.h"
#include "cgraph.h"
#include "coretypes.h"
#include "tm.h"
#include "tree.h"
#include "tree-flow.h"
#include "diagnostic.h"
#include "tree-pass.h"
#include "timevar.h"
#include "alloc-pool.h"
#include "params.h"
#include "ggc.h"
#include "vec.h"
#include<set>
#include<list>
#include<vector>
#include <tr1/tuple>
#include<map>
#define FUNC_COUNT 50000

using namespace std;
using namespace std::tr1;

extern list< struct cgraph_node * > func_worklist;

extern unsigned int num_bb_count;
extern unsigned int call_site_count;	

typedef tuple< unsigned int, unsigned int > callpt_type;

typedef set< callpt_type > set_call_pts;

extern list<struct cgraph_node * >::reverse_iterator cnode_it;
extern set< unsigned int > nodes_visited_callees;
//extern struct cgraph_node * func_array[INFINITY];

extern double preprocessing_time;
extern double interval_analysis_time;
extern unsigned int call_depth;

#if 1
extern unsigned int index_func_array[FUNC_COUNT];
extern unsigned int func_index_array[FUNC_COUNT];

extern bool function_worklist[FUNC_COUNT];
extern bool preprocess_worklist[FUNC_COUNT];

extern unsigned int index_func_array_d[FUNC_COUNT];
extern unsigned int func_index_array_d[FUNC_COUNT];
extern bool function_worklist_d[FUNC_COUNT];

#endif

#if 0
extern unsigned int *index_func_array;
extern unsigned int *func_index_array;

extern unsigned int *index_func_array_d;
extern unsigned int *func_index_array_d;

extern bool *function_worklist;
extern bool *preprocess_worklist;
extern bool *function_worklist_d;

#endif

extern FILE *f;

extern unsigned int func_count_d;

extern unsigned int func_count;

extern unsigned int func_num;

//extern map< int, struct cgraph_node * > func_numbering;

/* -----------------------------------------------------------------------------------
   Data structures picked up (and possibly modified) from tree-ssa-structalias.h file.
   -----------------------------------------------------------------------------------*/

struct csvariable_info
{
  /* ID of this variable  */
  unsigned int id;

  /* True for variables whose size is not known or variable.  */
  unsigned int is_unknown_size_var : 1;

  /* True for (sub-)fields that represent a whole variable.  */
  unsigned int is_full_var : 1;

  /* True if this field may contain pointers.  */
  unsigned int may_have_pointers : 1;

  /* True if it is a heap var. */
  unsigned int is_heap_var : 1;

  /* True if it is artificial var. */
  unsigned int is_art_var : 1;  // Added by Pritam

  /* True if this represents a global variable.  */
  unsigned int is_global_var : 1;

  /* A link to the variable for the next field in this structure.  */
  struct csvariable_info *next;

  /* Offset of this variable, in bits, from the base variable  */
  unsigned HOST_WIDE_INT offset;

  /* Size of the variable, in bits.  */
  unsigned HOST_WIDE_INT size;

  /* Full size of the base variable, in bits.  */
  unsigned HOST_WIDE_INT fullsize;

  /* Name of this variable */
  const char *name;

  /* Tree that this variable is associated with.  */
  tree decl;

  /* The list of all the constraints {aliases} that have this 
     variable as their LHS */
  //df_list constraints_with_vi_as_lhs;

  /* The function in whose scope this variable is defined. */
  struct cgraph_node *scoping_function;
};
typedef struct csvariable_info *csvarinfo_t;

typedef enum {ADDRESSOF, SCALAR, DEREF, INFINITY} constraint_expr_type;

typedef enum {lhs_id = 1, rhs_id = 2} lhs_rhs;

typedef enum {no_compose, stack_comp, stack_struct, struct_comp} cases_for_compose;

/* Use 0x8000... as special unknown offset.  */
#define UNKNOWN_OFFSET ((HOST_WIDE_INT)-1 << (HOST_BITS_PER_WIDE_INT-1))

/* An expression that appears in a constraint.  */

struct constraint_expr
{
  /* Constraint type.  */
//  constraint_expr_type 
  int type;

  /* Variable we are referring to in the constraint.  */
  unsigned int var;

  bool ptr_arith; // Boolean added for pointer arithmetic - Added by Pritam	

  /* Offset, in bits, of this constraint from the beginning of
     variables it ends up referring to.

     IOW, in a deref constraint, we would deref, get the result set,
     then add OFFSET to each member.   */
  HOST_WIDE_INT offset;

  // Vini, June'15
  constraint_expr ()
  {
	ptr_arith = false;
  }
};

typedef struct constraint_expr ce_s;
DEF_VEC_O(ce_s);
DEF_VEC_ALLOC_O(ce_s, heap);

struct constraint
{
  struct constraint_expr lhs;
  struct constraint_expr rhs;
  bool heap_alloc;	
};
typedef struct constraint *constraint_t;

/* This structure is used during pushing fields onto the fieldstack
   to track the offset of the field, since bitpos_of_field gives it
   relative to its immediate containing type, and we want it relative
   to the ultimate containing object.  */

struct fieldoff		/* Look into */
{
  /* Offset from the base of the base containing object to this field.  */
  HOST_WIDE_INT offset;

  /* Size, in bits, of the field.  */
  unsigned HOST_WIDE_INT size;

  unsigned has_unknown_size : 1;

  unsigned must_have_pointers : 1;

  unsigned may_have_pointers : 1;

  unsigned only_restrict_pointers : 1;
};
typedef struct fieldoff fieldoff_s;

DEF_VEC_O(fieldoff_s);
DEF_VEC_ALLOC_O(fieldoff_s,heap);


/*----------------------
  Variable Declarations.
  ---------------------*/
#define SSAVAR(x) (TREE_CODE (x) == SSA_NAME ? SSA_NAME_VAR (x) : x)
#define alloc_mem ggc_alloc_cleared_atomic 
#define total_bbs n_basic_blocks-NUM_FIXED_BLOCKS

enum {undef_id = 0, nothing_id = 1, escaped_id = 2, readonly_id = 3};

extern struct pointer_map_t *vi_for_tree;
//extern alloc_pool constraint_pool;

/*--------------------------------
  VEC data structure declarations.
  -------------------------------*/
DEF_VEC_P(csvarinfo_t);
DEF_VEC_ALLOC_P(csvarinfo_t, heap);
 extern  VEC(csvarinfo_t, heap) *csvarmap;
DEF_VEC_P(constraint_t);
DEF_VEC_ALLOC_P(constraint_t,heap);
 extern  VEC(constraint_t, heap) *aliases;

//extern VEC(constraint_t,heap) *constraints;
extern list<struct cgraph_node * > order_func;

extern alloc_pool constraint_pool;
extern alloc_pool csvarinfo_pool;

extern basic_block main_firstbb;
extern struct cgraph_node * main_cnode;

extern bool multi_rhs;
extern bool compute_only_pinfo;
extern bool compute_alias_and_pinfo;
extern bool check_deref;
extern bool deref_stmt;

extern set<unsigned int> CDV;
extern set<unsigned int> globals;

extern list<basic_block> worklist;

gimple bb_call_stmt (basic_block bb);
basic_block end_bb_of_fn (struct cgraph_node *node);
//set< unsigned int > end_bb_of_fn (struct cgraph_node *node);
int fieldoff_compare (const void *pa, const void *pb);
void cs_get_constraint_for (tree t, VEC (ce_s, heap) **results);
  csvarinfo_t cs_create_func_info_for (tree decl, const char *name);
	basic_block start_bb_of_fn (struct cgraph_node *node);
//	basic_block end_bb_of_fn (struct cgraph_node *node);
	HOST_WIDE_INT bitpos_of_field (const tree fdecl);
	constraint_t new_constraint (const struct constraint_expr lhs,const struct constraint_expr rhs);
	bool constraint_expr_equal (struct constraint_expr a, struct constraint_expr b);
	bool constraint_equal (struct constraint a, struct constraint b);
	const char * alias_get_name (tree decl);
	inline bool var_can_have_subvars (const_tree v);
	bool type_must_have_pointers (tree t);
	bool field_must_have_pointers (tree t);
	bool push_fields_onto_fieldstack (tree type, VEC(fieldoff_s,heap) **fieldstack,HOST_WIDE_INT offset);
	unsigned int count_num_arguments (tree decl, bool *is_varargs);
	bool check_for_overlaps (VEC (fieldoff_s,heap) *fieldstack);
	void sort_fieldstack (VEC(fieldoff_s,heap) *fieldstack);
	inline csvarinfo_t cs_get_varinfo (unsigned int n);
	void cs_insert_vi_for_tree (tree t, csvarinfo_t vi);
	bool is_proper_var (unsigned int varid);
	bool parm_decl (unsigned int varid);

//	void check (VEC(fieldoff_s,heap) *fieldstack );	
	struct cgraph_node * scoping_fn (unsigned int varid);
	bool var_defined_in_cfun (unsigned int varid, struct cgraph_node * cnode);
	bool global_var (unsigned int varid);
	bool art_var (unsigned int varid);
	bool unexpandable_var (unsigned int var, HOST_WIDE_INT offset);
	void cs_get_constraint_for_rhs (tree t, VEC (ce_s, heap) **results, basic_block bb, struct cgraph_node * cnode);
	csvarinfo_t cs_new_var_info (tree t, const char *name, struct cgraph_node * cnode);
	csvarinfo_t cs_create_variable_info_for_1 (tree decl, const char *name, struct cgraph_node * cnode);
	unsigned int cs_create_variable_info_for (tree decl, const char *name, basic_block bb, struct cgraph_node * cnode);
	csvarinfo_t cs_get_vi_for_tree (tree stmt, basic_block bb, struct cgraph_node * cnode);
	csvarinfo_t cs_lookup_vi_for_tree (tree t);
	struct constraint_expr cs_new_scalar_tmp_constraint_exp (const char *name, struct cgraph_node * cnode);
	tree build_fake_var_decl (tree type);
	csvarinfo_t cs_make_heapvar_for (csvarinfo_t lhs, const char *name, struct cgraph_node * cnode);
	void cs_make_constraint_from (csvarinfo_t vi, int from, basic_block bb);
	csvarinfo_t cs_make_constraint_from_heapvar (csvarinfo_t lhs, const char *name, basic_block bb, struct cgraph_node * cnode);
	csvarinfo_t cs_first_or_preceding_vi_for_offset (csvarinfo_t start,unsigned HOST_WIDE_INT offset);
	void cs_do_deref (VEC (ce_s, heap) **constraints, basic_block bb, struct cgraph_node * cnode);
	void cs_get_constraint_for_ptr_offset (tree ptr, tree offset,VEC (ce_s, heap) **results, basic_block bb, struct cgraph_node * cnode);
	void cs_get_constraint_for_component_ref (tree t, VEC(ce_s, heap) **results,bool address_p, bool lhs_p, basic_block bb, struct cgraph_node * cnode);
	void cs_get_constraint_for_ssa_var (tree t, VEC(ce_s, heap) **results, bool address_p, basic_block bb, struct cgraph_node * cnode);
	void cs_get_constraint_for_1 (tree t, VEC (ce_s, heap) **results, bool address_p, bool lhs_p, basic_block bb, struct cgraph_node * cnode);
	void cs_process_all_all_constraints (VEC (ce_s, heap) *lhsc, VEC (ce_s, heap) *rhsc, basic_block bb);
	void cs_get_constraint_for_address_of (tree t, VEC (ce_s, heap) **results, basic_block bb, struct cgraph_node * cnode);
	void cs_get_constraint_for (tree t, VEC (ce_s, heap) **results, basic_block bb, struct cgraph_node * cnode);
	csvarinfo_t cs_create_func_info_for (tree decl, const char *name, struct cgraph_node * cnode);
	csvarinfo_t cs_first_vi_for_offset (csvarinfo_t start, unsigned HOST_WIDE_INT offset);
	void cs_do_structure_copy (tree lhsop, tree rhsop, basic_block bb, struct cgraph_node * cnode);
	void cs_init_base_vars (struct cgraph_node * cnode);
	void cs_init_alias_vars (struct cgraph_node * cnode);
	tree cs_get_var (tree t);
	void insert_alias_in_pool (constraint_t t, csvarinfo_t vi, basic_block bb);
	void append_to_bb_constraints (unsigned int,bool, basic_block bb);
	void cs_process_constraint (constraint_t t, basic_block bb);
	bool possibly_deref (gimple stmt);
	bool associate_varinfo_to_alias (struct cgraph_node *node, void *data);
	void process_library_call (gimple stmt, basic_block bb, struct cgraph_node * cnode);
	void map_arguments_at_call (gimple stmt, tree decl, bool generate_liveness, basic_block bb, struct cgraph_node * cnode);
	void map_function_arguments (struct cgraph_node * src_function, basic_block call_block, gimple call_stmt, struct cgraph_node * called_function);
	void map_return_value (struct cgraph_node * src_function, basic_block call_block, basic_block callee_end_block, struct cgraph_node * called_function);

	
	void process_gimple_assign_stmt (gimple, basic_block bb, struct cgraph_node * cnode);
	void process_gimple_condition(gimple, basic_block bb, struct cgraph_node * cnode);
	void process_gimple_phi_stmt (gimple, basic_block bb, struct cgraph_node * cnode);
	
	bool is_gimple_endblock (gimple t);
	void generate_retval_liveness (gimple stmt, basic_block bb, struct cgraph_node * cnode);
	bool process_phi_pointers (basic_block bb, struct cgraph_node * cnode);
	tree get_called_fn_decl (gimple stmt);
	void generate_liveness_constraint(basic_block bb, unsigned int id);

//	void init_bb_aux(basic_block bb);
//	void end_bb_aux(basic_block bb);

	// Basic block is passed by reference, since we need to update the basic block 
	// to the current program split, which will be in a new block after block splitting.
	gimple_stmt_iterator split_bb_at_stmt (basic_block & bb, gimple stmt, struct cgraph_node * cnode);
	void initialize_block_aux (basic_block block, struct cgraph_node * cnode);
	gimple_stmt_iterator split_block_at_stmt (gimple statement, basic_block block, struct cgraph_node *cnode);

	void initialization (void);
	void preprocess_control_flow_graph ();
	void restore_control_flow_graph ();
	void print_parsed_data (basic_block current_block);
	void print_parsed_data ();
	void print_original_cfg ();
	void print_variable_data (int index);
	void print_assignment_data (int index);
	void print_variable_data ();
	void print_assignment_data ();

	void delete_block_aux ();
	void init_fn_aux();
	void end_fn_aux();

	bool associate_varinfo_to_alias (struct cgraph_node *node, void *data);


	bool is_cdv(unsigned int id);
	unsigned int context_dep(unsigned int id);
	unsigned int context_dep_rev(unsigned int id);
	void create_cdv(csvarinfo_t var);
	void initialize_liveness(basic_block bb, struct cgraph_node *cnode);

//	bblist get_pred(basic_block bb, struct cgraph_node *cnode);
//	bblist get_succ(basic_block bb, struct cgraph_node *cnode);

	bool multiple_pred(basic_block bb, struct cgraph_node *cnode);
	bool multiple_succ(basic_block bb, struct cgraph_node *cnode);
	
	void create_con_dep_node(unsigned int);
	const char * copy_string(const char * var);
	void boundary_info(struct cgraph_node *);
	const char * get_var_name(unsigned int);
	void set_boundary_points();
	void set_boundary_live();
	struct cgraph_node * cnode_of_bb (basic_block bb);
	bool is_function_worklist_empty();
	bool is_function_worklist_d_empty();
	void create_depth_ordering();
	void depth_ordering();
	void get_total_cnodes(struct cgraph_node *cnode);
	void get_pred_count(struct cgraph_node *cnode);
	void preprocess_cnode(struct cgraph_node *cnode);
	bool call_indirectly(struct cgraph_node *cnode);
	void construct_summary_flow_function_of_bb();
	void get_trans_callees(struct cgraph_node *);
	void get_callees();

#endif
