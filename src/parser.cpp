#include "block_information.hpp"
#include "dataflow.hpp"
#include "cgraph_node.hpp"
#include "parser.hpp"
#include "interval.hpp"
#include <string.h> 

list<struct cgraph_node * > order_func;
basic_block main_firstbb = NULL;
bool multi_rhs = false;
bool compute_only_pinfo = false;
bool compute_alias_and_pinfo = false;
//bool all_contexts_together = true;
bool check_deref = false;
bool deref_stmt = false;
alloc_pool constraint_pool;
alloc_pool csvarinfo_pool;
VEC(csvarinfo_t, heap) *csvarmap;
VEC(constraint_t, heap) *aliases;
VEC(constraint_t,heap) *constraints;
struct pointer_map_t *vi_for_tree;
struct cgraph_node * main_cnode;
set<unsigned int> CDV;
set<unsigned int> globals;

//list<basic_block> worklist;

list< struct cgraph_node * > func_worklist;

set< struct cgraph_node * > indirect_cnodes;

list<struct cgraph_node * >::reverse_iterator cnode_it;

unsigned int num_bb_count = 0;
unsigned int call_site_count = 0;	

double preprocessing_time = 0;
double interval_analysis_time = 0;

double temptime = 0;

FILE *f;

#if 1
unsigned int index_func_array[FUNC_COUNT];
unsigned int func_index_array[FUNC_COUNT];

unsigned int index_func_array_d[FUNC_COUNT];
unsigned int func_index_array_d[FUNC_COUNT];

bool function_worklist[FUNC_COUNT];
bool preprocess_worklist[FUNC_COUNT];
bool function_worklist_d[FUNC_COUNT];
#endif

#if 0
unsigned int *index_func_array;
unsigned int *func_index_array;

unsigned int *index_func_array_d;
unsigned int *func_index_array_d;

bool *function_worklist;
bool *preprocess_worklist;
bool *function_worklist_d;

#endif


unsigned int func_count = 1;
unsigned int func_count_d = 1;
unsigned int test_func_count = 0;

unsigned int func_num = 0;

set< struct cgraph_node * > set_cnodes_call_graph;
bool print = false;

void create_undef_node()
{
	node_id id = make_tuple(0, 1, 0);

	il il1;
	il1.add_deref(-1);

	undef_node.set_var_id(undef_id);
	undef_node.set_ind_list(il1);
	
	undef_node.set_node_id(id);

	vec_nodes temp;

	temp.push_back(undef_node);

	node_map[undef_id][1] = temp;

}

bool associate_varinfo_to_alias (struct cgraph_node *node, void *data)
{      
  if (node->alias || node->thunk.thunk_p)
    cs_insert_vi_for_tree (node->decl, (csvarinfo_t)data);
  return false;
}  

/* Return the node to which the basic block belongs. */
#if 0
struct cgraph_node * cnode_of_bb (basic_block bb)
{
   return (struct cgraph_node *) (((block_information)(bb->aux)).get_cfun());
}
#endif

gimple bb_call_stmt (basic_block bb)
{
   gimple_stmt_iterator gsi;
   gimple stmt;
   for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi)) {
      stmt = gsi_stmt (gsi);
      if (is_gimple_call (stmt))
         return stmt;
   }
   return NULL;
}

basic_block start_bb_of_fn (struct cgraph_node *node)
{
	basic_block bb = ENTRY_BLOCK_PTR_FOR_FUNCTION (DECL_STRUCT_FUNCTION (node->decl));
	basic_block nn;
         edge e;
        edge_iterator ei;

//        if(((block_information *)(bb->aux))->end_block)
//              return nn;

        #if 1
        FOR_EACH_EDGE(e,ei,bb->succs)
        {
                if(e->dest == NULL)
                        continue;

                basic_block bt = e->dest;

//                fprintf(dump_file,"\nSucc of Entry Block %d -> %d %s\n", bb->index, bt->index, cgraph_node_name(node));

//		return bt;
        }
	#endif
	
   return ENTRY_BLOCK_PTR_FOR_FUNCTION (DECL_STRUCT_FUNCTION (node->decl))->next_bb;
}

basic_block end_bb_of_fn (struct cgraph_node *node)
{
	//fprintf (dump_file, "\nend_bb_of_fn");
	unsigned int x = ((function_info *)(node->aux))->end_block_id;
	//fprintf (dump_file, "\nx=%d", x);

	basic_block bb;

	struct function *fn;
	
	fn = DECL_STRUCT_FUNCTION(node->decl);

	if(x == 0)
	{
		bb = EXIT_BLOCK_PTR_FOR_FUNCTION (DECL_STRUCT_FUNCTION (node->decl))->prev_bb;
		//fprintf (dump_file, "\nEXIT");
	}
	else
	{
		bb = BASIC_BLOCK_FOR_FUNCTION(fn, x);
		//fprintf (dump_file, "\nRETURN");
	}

	return bb;

}

/* Return the position, in bits, of FIELD_DECL from the beginning of its
   structure.  */

HOST_WIDE_INT bitpos_of_field (const tree fdecl)
{
  if (!host_integerp (DECL_FIELD_OFFSET (fdecl), 0)
      || !host_integerp (DECL_FIELD_BIT_OFFSET (fdecl), 0))
    return -1;

  return (TREE_INT_CST_LOW (DECL_FIELD_OFFSET (fdecl)) * BITS_PER_UNIT
          + TREE_INT_CST_LOW (DECL_FIELD_BIT_OFFSET (fdecl)));
}

/* Create a new constraint consisting of LHS and RHS expressions.  */

constraint_t new_constraint (const struct constraint_expr lhs,
                const struct constraint_expr rhs)
{
  constraint_t ret = (constraint_t) pool_alloc (constraint_pool);
  ret->lhs = lhs;
  ret->rhs = rhs;
  ret->heap_alloc = false;	
  return ret;
}

/* Return true if two constraint expressions A and B are equal.  */

bool constraint_expr_equal (struct constraint_expr a, struct constraint_expr b)
{
  return a.type == b.type && a.var == b.var && a.offset == b.offset;
}

/* Return true if two constraints A and B are equal.  */

bool constraint_equal (struct constraint a, struct constraint b)
{
  return constraint_expr_equal (a.lhs, b.lhs)
    && constraint_expr_equal (a.rhs, b.rhs);
}

/* Return a printable name for DECL  */

const char * alias_get_name (tree decl)
{
  const char *res;
  char *temp;
  int num_printed = 0;

  if (DECL_ASSEMBLER_NAME_SET_P (decl))
    res = IDENTIFIER_POINTER (DECL_ASSEMBLER_NAME (decl));
  else
    res= get_name (decl);
  if (res != NULL)
    return res;

  res = "NULL";
  if (!dump_file)
    return res;

  if (TREE_CODE (decl) == SSA_NAME)
    {
      num_printed = asprintf (&temp, "%s_%u",
                              alias_get_name (SSA_NAME_VAR (decl)),
                              SSA_NAME_VERSION (decl));
    }
  else if (DECL_P (decl))
    {
      num_printed = asprintf (&temp, "D.%u", DECL_UID (decl));
    }
  if (num_printed > 0)
    {
      res = ggc_strdup (temp);
      free (temp);
    }
  return res;
}

/* Return true if V is a tree that we can have subvars for.
   Normally, this is any aggregate type.  Also complex
   types which are not gimple registers can have subvars.  */

bool var_can_have_subvars (const_tree v)
{
  /* Volatile variables should never have subvars.  */
  if (TREE_THIS_VOLATILE (v))
  {
    return false;
  }

  /* Non decls or memory tags can never have subvars.  */
  if (!DECL_P (v))
  {
    return false;
  }

  /* Aggregates without overlapping fields can have subvars.  */
  if (TREE_CODE (TREE_TYPE (v)) == RECORD_TYPE)
  {
    return true;
  }

  return false;
}

/* Return true if T is a type that does contain pointers.  */

bool type_must_have_pointers (tree t)
{
  if (POINTER_TYPE_P (t))
  {
    return true;
  }

  if (TREE_CODE (t) == ARRAY_TYPE)
  {
    return type_must_have_pointers (TREE_TYPE (t));
  }

  /* A function or method can have pointers as arguments, so track
     those separately.  */
  if (TREE_CODE (t) == FUNCTION_TYPE
      || TREE_CODE (t) == METHOD_TYPE)
  {
    return true;
  }

  if (RECORD_OR_UNION_TYPE_P (t))
  {
    return true;
  }

  return false;
}

bool field_must_have_pointers (tree t)
{
  return type_must_have_pointers (TREE_TYPE (t));
}


/* Given a TYPE, and a vector of field offsets FIELDSTACK, push all
   the fields of TYPE onto fieldstack, recording their offsets along
   the way.

   OFFSET is used to keep track of the offset in this entire
   structure, rather than just the immediately containing structure.
   Returns false if the caller is supposed to handle the field we
   recursed for.  */

/*
void check (VEC(fieldoff_s,heap) *fieldstack )
{
       if (VEC_length (fieldoff_s, fieldstack) <= 1
          || VEC_length (fieldoff_s, fieldstack) > MAX_FIELDS_FOR_FIELD_SENSITIVE) {
       }
       else
}
*/

bool push_fields_onto_fieldstack (tree type, VEC(fieldoff_s,heap) **fieldstack, HOST_WIDE_INT offset)
{

	  return false;
  /***-----tree field;
  bool empty_p = true;

  if (TREE_CODE (type) != RECORD_TYPE)
    return false;


  /-- If the vector of fields is growing too big, bail out early.
     Callers check for VEC_length <= MAX_FIELDS_FOR_FIELD_SENSITIVE, make
     sure this fails.  ---/
  if (VEC_length (fieldoff_s, *fieldstack) > MAX_FIELDS_FOR_FIELD_SENSITIVE)
    return false;


  for (field = TYPE_FIELDS (type); field; field = DECL_CHAIN (field))
    if (TREE_CODE (field) == FIELD_DECL)
      {
        bool push = false;
        HOST_WIDE_INT foff = bitpos_of_field (field);

        if (!var_can_have_subvars (field)
            || TREE_CODE (TREE_TYPE (field)) == QUAL_UNION_TYPE
            || TREE_CODE (TREE_TYPE (field)) == UNION_TYPE)
          push = true;
        else if (!push_fields_onto_fieldstack
                    (TREE_TYPE (field), fieldstack, offset + foff)
                 && (DECL_SIZE (field)
                     && !integer_zerop (DECL_SIZE (field))))
	{
          /--- Empty structures may have actual size, like in C++.  So
             see if we didn't push any subfields and the size is
             nonzero, push the field onto the stack.  ---/
//	  check (*fieldstack);
          push = true;
	}

        if (push)
          {
            fieldoff_s *pair = NULL;
            bool has_unknown_size = false;
            bool must_have_pointers_p;

            if (!VEC_empty (fieldoff_s, *fieldstack))
	    {
//	      check (*fieldstack);
              pair = VEC_last (fieldoff_s, *fieldstack);
            }

            /---- If there isn't anything at offset zero, create sth.  ---/
            if (!pair
                && offset + foff != 0)
              {
                pair = VEC_safe_push (fieldoff_s, heap, *fieldstack, NULL);
                pair->offset = 0;
                pair->size = offset + foff;
                pair->has_unknown_size = false;
                pair->must_have_pointers = false;
                pair->may_have_pointers = false;
                pair->only_restrict_pointers = false;
              }

            if (!DECL_SIZE (field)
                || !host_integerp (DECL_SIZE (field), 1))
              has_unknown_size = true;

//	    check (*fieldstack);

            /---- If adjacent fields do not contain pointers merge them.  ---/
            must_have_pointers_p = field_must_have_pointers (field);
            if (pair
                && !has_unknown_size
                && !must_have_pointers_p
                && !pair->must_have_pointers
                && !pair->has_unknown_size
                && pair->offset + (HOST_WIDE_INT)pair->size == offset + foff)
              {
                pair->size += TREE_INT_CST_LOW (DECL_SIZE (field));
              }
            else
              {
//	        check (*fieldstack);
                pair = VEC_safe_push (fieldoff_s, heap, *fieldstack, NULL);	// PROBLEM: fieldstack not working
//	        check (*fieldstack);
                pair->offset = offset + foff;
                pair->has_unknown_size = has_unknown_size;
                if (!has_unknown_size)
                  pair->size = TREE_INT_CST_LOW (DECL_SIZE (field));
                else
                  pair->size = -1;
                pair->must_have_pointers = must_have_pointers_p;
                pair->may_have_pointers = true;
                pair->only_restrict_pointers
                  = (!has_unknown_size
                     && POINTER_TYPE_P (TREE_TYPE (field))
                     && TYPE_RESTRICT (TREE_TYPE (field)));
              }
//	      check (*fieldstack);
          }

//	check (*fieldstack);
        empty_p = false;
      }

  return !empty_p;*/
}

/* Count the number of arguments DECL has, and set IS_VARARGS to true
   if it is a varargs function.  */

unsigned int count_num_arguments (tree decl, bool *is_varargs)
{
  unsigned int num = 0;
  tree t;

  /* Capture named arguments for K&R functions.  They do not
     have a prototype and thus no TYPE_ARG_TYPES.  */
  for (t = DECL_ARGUMENTS (decl); t; t = DECL_CHAIN (t))
    ++num;

  /* Check if the function has variadic arguments.  */
  for (t = TYPE_ARG_TYPES (TREE_TYPE (decl)); t; t = TREE_CHAIN (t))
    if (TREE_VALUE (t) == void_type_node)
      break;
  if (!t)
    *is_varargs = true;

  return num;
}

/* Return true if FIELDSTACK contains fields that overlap.
   FIELDSTACK is assumed to be sorted by offset.  */

bool check_for_overlaps (VEC (fieldoff_s,heap) *fieldstack)
{
  fieldoff_s *fo = NULL;
  unsigned int i;
  HOST_WIDE_INT lastoffset = -1;

  FOR_EACH_VEC_ELT (fieldoff_s, fieldstack, i, fo)
    {
      if (fo->offset == lastoffset)
        return true;
      lastoffset = fo->offset;
    }
  return false;
}

/* qsort comparison function for two fieldoff's PA and PB */
// This function cannot be made a member function of this class

int fieldoff_compare (const void *pa, const void *pb)
{
  const fieldoff_s *foa = (const fieldoff_s *)pa;
  const fieldoff_s *fob = (const fieldoff_s *)pb;
  unsigned HOST_WIDE_INT foasize, fobsize;

  if (foa->offset < fob->offset)
    return -1;
  else if (foa->offset > fob->offset)
    return 1;

  foasize = foa->size;
  fobsize = fob->size;
  if (foasize < fobsize)
    return -1;
  else if (foasize > fobsize)
    return 1;
  return 0;
}

/* Sort a fieldstack according to the field offset and sizes.  */

void sort_fieldstack (VEC(fieldoff_s,heap) *fieldstack)
{
  VEC_qsort (fieldoff_s, fieldstack, fieldoff_compare);
}

/*----------------------------------------------------------------------
  The base implementation. The method implements points-to analysis
  using callstrings method. All the functions that have _cs_ 
  prepended to their names have been lifted from tree-ssa-structalias.c
  ---------------------------------------------------------------------*/

/* Return the varmap element N */

csvarinfo_t cs_get_varinfo (unsigned int n)
{
   return VEC_index (csvarinfo_t, csvarmap, n);
}

/* Insert ID as the variable id for tree T in the vi_for_tree map.  */

void cs_insert_vi_for_tree (tree t, csvarinfo_t vi)
{
   void **slot = pointer_map_insert (vi_for_tree, t);
   gcc_assert (vi);
   gcc_assert (*slot == NULL);
   *slot = vi;
}

bool is_proper_var (unsigned int varid)
{
   return (varid > 2);
}

bool parm_decl (unsigned int varid)
{
   return (TREE_CODE (SSAVAR (cs_get_varinfo (varid)->decl))
          == PARM_DECL);
}

struct cgraph_node * scoping_fn (unsigned int varid)
{
   return cs_get_varinfo (varid)->scoping_function;
}

bool var_defined_in_cfun (unsigned int varid, struct cgraph_node * cnode)
{
   return (cnode == scoping_fn (varid));
}

bool global_var (unsigned int varid)
{
   return (cs_get_varinfo (varid)->is_global_var);
}

bool art_var (unsigned int varid)
{
   return (cs_get_varinfo (varid)->is_art_var);
}

bool unexpandable_var (unsigned int var, HOST_WIDE_INT offset)
{
   return (offset == 0 ||
           !is_proper_var (var) ||
           offset == UNKNOWN_OFFSET ||
           cs_get_varinfo (var)->is_heap_var);
}

/* Given a gimple tree T, return the constraint expression vector for it
   to be used as the rhs of a constraint.  */

void cs_get_constraint_for_rhs (tree t, VEC (ce_s, heap) **results, basic_block bb, struct cgraph_node * cnode)
{
   gcc_assert (VEC_length (ce_s, *results) == 0);
   cs_get_constraint_for_1 (t, results, false, false, bb, cnode);
}

void create_cdv(csvarinfo_t var)
{
//   	unsigned index = VEC_length (csvarinfo_t, csvarmap);

	csvarinfo_t ret_cdv = (csvarinfo_t) pool_alloc (csvarinfo_pool);
	ret_cdv->id = var->id + 1;
//	ret_cdv->name = var->name; // cdv_name;
//	string str = std::string(var->name);
//	ret_cdv->name = str.c_str(); // cdv_name;
	char *temp = (char *)xmalloc(strlen(var->name)+1);
	strcpy(temp,var->name);
//	ret_cdv->name = strdup(var->name); // cdv_name;
	ret_cdv->name = (const char *)temp;
	ret_cdv->decl = var->decl;
	ret_cdv->is_unknown_size_var = var->is_unknown_size_var;
	ret_cdv->is_full_var = var->is_full_var;
	ret_cdv->is_heap_var = var->is_heap_var;
	ret_cdv->may_have_pointers = var->may_have_pointers;
	ret_cdv->is_global_var = var->is_global_var;
	ret_cdv->scoping_function = var->scoping_function;
	ret_cdv->next = NULL;
	VEC_safe_push (csvarinfo_t, heap, csvarmap, ret_cdv);

	CDV.insert(ret_cdv->id);
	create_con_dep_node(ret_cdv->id);
}

void create_con_dep_node(unsigned int x)
{
	Node n;
	
	n.set_var_id(x);

	il ilt;

	ilt.add_deref(-1);
	n.set_ind_list(ilt);

	n.add_node_map();
}

/* Return a new variable info structure consisting for a variable
   named NAME, and using constraint graph node NODE.  Append it
   to the vector of variable info structures.  */
csvarinfo_t cs_new_var_info (tree t, const char *name, struct cgraph_node * cnode)
{
   unsigned index = VEC_length (csvarinfo_t, csvarmap);
   csvarinfo_t ret = (csvarinfo_t) pool_alloc (csvarinfo_pool);
	
   ret->id = index;
   ret->name = name;
   ret->decl = t;
   ret->is_unknown_size_var = false;
   ret->is_full_var = (t == NULL_TREE);
   ret->is_heap_var = false;
   ret->is_art_var = false; // Added by Pritam
   ret->may_have_pointers = true;
   ret->is_global_var = (t == NULL_TREE);
   /* Vars without decl are artificial and do not have sub-variables.  */
   if (t && DECL_P (t))
     ret->is_global_var = (is_global_var (t)
                          /* We have to treat even local register variables
                             as escape points.  */
                          || (TREE_CODE (t) == VAR_DECL
                              && DECL_HARD_REGISTER (t)));
   //ret->constraints_with_vi_as_lhs = NULL;
//   ret->scoping_function = (ret->is_global_var) ? NULL : cnode;
   ret->scoping_function = cnode;
   ret->next = NULL;

   VEC_safe_push (csvarinfo_t, heap, csvarmap, ret); 

   // Vini, June'15: Commented out
//   if(ret->is_global_var)
//   {	
//	globals.insert(index);	
//   }

   // Vini, June'15: Look into this. This code is generating duplicate entries
   // of the same variable. 
//   if(ret->id > 4)
//   {
//        create_cdv(ret);
//   }

   return ret;
}

/* Create a varinfo structure for NAME and DECL, and add it to VARMAP.
   This will also create any varinfo structures necessary for fields
   of DECL.  */

csvarinfo_t cs_create_variable_info_for_1 (tree decl, const char *name, struct cgraph_node * cnode)
{

   csvarinfo_t vi, newvi;
   tree decl_type = TREE_TYPE (decl);
   tree declsize = DECL_P (decl) ? DECL_SIZE (decl) : TYPE_SIZE (decl_type);
   VEC (fieldoff_s,heap) *fieldstack = NULL;
   fieldoff_s *fo;
   unsigned int i;

   if (!declsize || !host_integerp (declsize, 1)) {
      vi = cs_new_var_info (decl, name, cnode);
      vi->offset = 0;
      vi->size = ~0;
      vi->fullsize = ~0;
      vi->is_unknown_size_var = true;
      vi->is_full_var = true;
      vi->may_have_pointers = true;
      return vi;
   }
   /* Collect field information.  */
   if (var_can_have_subvars (decl)
      /* ???  Force us to not use subfields for global initializers
	 in IPA mode.  Else we'd have to parse arbitrary initializers.  */
      && !(is_global_var (decl) && DECL_INITIAL (decl))) {
//	fprintf(dump_file,"\nInside create variable %s\n",name);

       fieldoff_s *fo = NULL;
       bool notokay = false;
       unsigned int i;

	// Vini, June'15: Without this function, x.f is treated as x. For a
	// safe field-insensitive analysis, we should not call this function.
	 push_fields_onto_fieldstack (decl_type, &fieldstack, 0);
/*
       if (VEC_length (fieldoff_s, fieldstack) <= 1
          || VEC_length (fieldoff_s, fieldstack) > MAX_FIELDS_FOR_FIELD_SENSITIVE) {
       }
       else

       if (VEC_length (fieldoff_s, fieldstack) <= 1)
       if (VEC_length (fieldoff_s, fieldstack) > MAX_FIELDS_FOR_FIELD_SENSITIVE)
       else
*/

       for (i = 0; !notokay && VEC_iterate (fieldoff_s, fieldstack, i, fo); i++)
	   if (fo->has_unknown_size || fo->offset < 0) {
	       notokay = true;
	       break;
	   }

          /* We can't sort them if we have a field with a variable sized type,
 	  which will make notokay = true.  In that case, we are going to return
	  without creating varinfos for the fields anyway, so sorting them is a
	  waste to boot.  */
       if (!notokay) {

	   sort_fieldstack (fieldstack);
	   /* Due to some C++ FE issues, like PR 22488, we might end up
	      what appear to be overlapping fields even though they,
	      in reality, do not overlap.  Until the C++ FE is fixed,
	      we will simply disable field-sensitivity for these cases.  */
	   notokay = check_for_overlaps (fieldstack);
       }

       if (notokay)
	   VEC_free (fieldoff_s, heap, fieldstack);
   }

/*
   if (VEC_length (fieldoff_s, fieldstack) <= 1)
   if (VEC_length (fieldoff_s, fieldstack) > MAX_FIELDS_FOR_FIELD_SENSITIVE)
   else
*/

   /* If we didn't end up collecting sub-variables create a full
      variable for the decl.  */
   if (VEC_length (fieldoff_s, fieldstack) <= 1
      || VEC_length (fieldoff_s, fieldstack) > MAX_FIELDS_FOR_FIELD_SENSITIVE) {

       vi = cs_new_var_info (decl, name, cnode);
       vi->offset = 0;
       vi->may_have_pointers = true;
       vi->fullsize = TREE_INT_CST_LOW (declsize);
       vi->size = vi->fullsize;
       vi->is_full_var = true;
       VEC_free (fieldoff_s, heap, fieldstack);
       return vi;
   }


   vi = cs_new_var_info (decl, name, cnode);
   vi->fullsize = TREE_INT_CST_LOW (declsize);
   for (i = 0, newvi = vi;
       VEC_iterate (fieldoff_s, fieldstack, i, fo);
       ++i, newvi = newvi->next) {


       const char *newname = "NULL";
       char *tempname;

       if (dump_file) {
	   asprintf (&tempname, "%s." HOST_WIDE_INT_PRINT_DEC
		    "+" HOST_WIDE_INT_PRINT_DEC, name, fo->offset,fo->size);
	   newname = ggc_strdup (tempname);
	   free (tempname);

       }
       newvi->name = newname;
       newvi->offset = fo->offset;
       newvi->size = fo->size;
       newvi->fullsize = vi->fullsize;
       newvi->may_have_pointers = fo->may_have_pointers;
       // newvi->only_restrict_pointers = fo->only_restrict_pointers;
       if (i + 1 < VEC_length (fieldoff_s, fieldstack))
	   newvi->next = cs_new_var_info (decl, name, cnode);
   }

   VEC_free (fieldoff_s, heap, fieldstack);
   if (vi)
 	  return vi;
}

unsigned int cs_create_variable_info_for (tree decl, const char *name, basic_block bb, struct cgraph_node * cnode)
{
   csvarinfo_t vi = cs_create_variable_info_for_1 (decl, name, cnode);
   unsigned int id = vi->id;

   cs_insert_vi_for_tree (decl, vi);

   /* Create initial constraints for globals.  */
   for (; vi; vi = vi->next) {
       if (!vi->may_have_pointers || !vi->is_global_var)
           continue;


       /* If this is a global variable with an initializer,
          generate constraints for it. */
       if (DECL_INITIAL (decl)) {
           VEC (ce_s, heap) *rhsc = NULL;
           struct constraint_expr lhs, *rhsp;
           unsigned i;
           cs_get_constraint_for_rhs (DECL_INITIAL (decl), &rhsc, bb, cnode);
           lhs.var = vi->id;
           lhs.offset = 0;
           lhs.type = SCALAR;
           FOR_EACH_VEC_ELT (ce_s, rhsc, i, rhsp)               // Vini: Why commented out????
               cs_process_constraint (new_constraint (lhs, *rhsp), bb);
           VEC_free (ce_s, heap, rhsc);                 // Vini: Why commented out????
       }
    }

   return id;
}


/* Find the variable id for tree T in the map. If T doesn't 
  exist in the map, create an entry for it and return it. */

csvarinfo_t cs_get_vi_for_tree (tree stmt, basic_block bb, struct cgraph_node * cnode)
{
   // Vini, June'15
   tree t = SSAVAR (stmt);
// tree t = stmt;
   void **slot = pointer_map_contains (vi_for_tree, t);
   if (slot == NULL)
   {
       csvarinfo_t vi = cs_get_varinfo (cs_create_variable_info_for (t, alias_get_name (t), bb, cnode));
       if (vi)
       return vi;
       //return cs_get_varinfo (cs_create_variable_info_for (t, alias_get_name (t), bb, cnode));
   }

   csvarinfo_t vi = (csvarinfo_t) *slot;
   if (vi)

   return (csvarinfo_t) *slot;
}

/* Find the variable info for tree T in VI_FOR_TREE. If T does not
   exist in the map, return NULL, otherwise, return the varinfo 
   we found.  */

csvarinfo_t cs_lookup_vi_for_tree (tree t)
{
   void **slot = pointer_map_contains (vi_for_tree, t);
   if (slot == NULL)
       return NULL;

   return (csvarinfo_t) *slot;
}

/* Get a scalar constraint expression for a new temporary variable.  */

struct constraint_expr cs_new_scalar_tmp_constraint_exp (const char *name, struct cgraph_node * cnode)
{
   struct constraint_expr tmp;
   csvarinfo_t vi;

   vi = cs_new_var_info (NULL_TREE, name, cnode);
   vi->offset = 0;
   vi->size = -1;
   vi->fullsize = -1;
   vi->is_full_var = 1;

   tmp.var = vi->id;
   tmp.type = SCALAR;
   tmp.offset = 0;

   return tmp;
}

/* CHANGE DUE TO GCC-4.7.2
   function make_heapvar_for of gcc-4.6.* is modified to make_heapvar in gcc-4.7.2.
   This cs_make_heapvar_for is also modified */

/* Temporary storage for fake var decls.  */
struct obstack fake_var_decl_obstack;

/* Build a fake VAR_DECL acting as referrer to a DECL_UID.  */

tree build_fake_var_decl (tree type)
{
  tree decl = (tree) XOBNEW (&fake_var_decl_obstack, struct tree_var_decl);
  memset (decl, 0, sizeof (struct tree_var_decl));
  TREE_SET_CODE (decl, VAR_DECL);
  TREE_TYPE (decl) = type;
  DECL_UID (decl) = allocate_decl_uid ();
  SET_DECL_PT_UID (decl, -1);
  layout_decl (decl, 0);
  return decl;
}

/* Create a new artificial heap variable with NAME.
   Return the created variable.  */

csvarinfo_t cs_make_heapvar_for (csvarinfo_t lhs, const char *name, struct cgraph_node * cnode)
{
  csvarinfo_t vi;
  tree heapvar;
  const char *newname = "NULL";
  char *tempname;

//  heapvar = build_fake_var_decl (ptr_type_node);


//  else	

  /* Append 'heap' with the its index in csvarinfo. */
  asprintf (&tempname, "%s.%d", name, VEC_length (csvarinfo_t, csvarmap));
  newname = ggc_strdup (tempname);

  heapvar = build_fake_var_decl (ptr_type_node);
  DECL_EXTERNAL (heapvar) = 1;
  vi = cs_new_var_info (heapvar, newname, cnode);

  //vi->is_artificial_var = true;
  vi->is_heap_var = true;
  vi->is_art_var = true;   // Added by Pritam
  vi->is_unknown_size_var = true;
  vi->offset = 0;
  vi->fullsize = ~0;
  vi->size = ~0;
  vi->is_full_var = true;
  cs_insert_vi_for_tree (heapvar, vi);

  return vi;
}

/* Create a constraint ID = &FROM. */
void cs_make_constraint_from (csvarinfo_t vi, int from, basic_block bb)
{
   struct constraint_expr lhs, rhs;

   lhs.var = vi->id;
   lhs.offset = 0;
   lhs.type = SCALAR;

   rhs.var = from;
   rhs.offset = 0;
   rhs.type = ADDRESSOF;
   cs_process_constraint (new_constraint (lhs, rhs), bb);
}

/* Create a new artificial heap variable with NAME and make a
   constraint from it to LHS.  Return the created variable.  */

csvarinfo_t cs_make_constraint_from_heapvar (csvarinfo_t lhs, const char *name, basic_block bb, struct cgraph_node * cnode)
{
   csvarinfo_t vi = cs_make_heapvar_for (lhs, name, cnode);
//   cs_do_structure_copy (lhs->decl, vi->decl, bb, cnode);	
   cs_make_constraint_from (lhs, vi->id, bb);
//   fprintf(dump_file,"\nHeap Object Created\n");	
   	
   return vi;
}

/* Find the first varinfo in the same variable as START that overlaps with
   OFFSET.  If there is no such varinfo the varinfo directly preceding
   OFFSET is returned.  */

csvarinfo_t cs_first_or_preceding_vi_for_offset (csvarinfo_t start, unsigned HOST_WIDE_INT offset)
{
   /* If we cannot reach offset from start, lookup the first field
      and start from there.  */
   if (start->offset > offset)
       start = cs_lookup_vi_for_tree (start->decl);

   /* We may not find a variable in the field list with the actual
      offset when when we have glommed a structure to a variable.
      In that case, however, offset should still be within the size
      of the variable.
      If we got beyond the offset we look for return the field
      directly preceding offset which may be the last field.  */
   while (start->next && offset >= start->offset
         && !((offset - start->offset) < start->size))
       start = start->next;

   return start;
}

/* Dereference the constraint expression CONS, and return the result.
   DEREF (ADDRESSOF) = SCALAR
   DEREF (SCALAR) = DEREF
   DEREF (DEREF) = (temp = DEREF1; result = DEREF(temp))
   This is needed so that we can handle dereferencing DEREF constraints.  */

void cs_do_deref (VEC (ce_s, heap) **constraints, basic_block bb, struct cgraph_node * cnode)
{
   struct constraint_expr *c;
   unsigned int i = 0;

   FOR_EACH_VEC_ELT (ce_s, *constraints, i, c) {
       //c->ptr_arith = false; 	
       if (c->type == SCALAR)
           c->type = DEREF;
       else if (c->type == ADDRESSOF)
           c->type = SCALAR;
       else if (c->type == DEREF) {
           struct constraint_expr tmplhs;
           tmplhs = cs_new_scalar_tmp_constraint_exp ("dereftmp", cnode);
           cs_process_constraint (new_constraint (tmplhs, *c), bb);
           c->var = tmplhs.var;
       }
       else
           gcc_unreachable ();
   }
}

/* Get constraint expressions for offsetting PTR by OFFSET.  Stores the
   resulting constraint expressions in *RESULTS.  */

void cs_get_constraint_for_ptr_offset (tree ptr, tree offset,
			       VEC (ce_s, heap) **results, basic_block bb, struct cgraph_node * cnode)
{
   struct constraint_expr c;
   unsigned int j, n;
   HOST_WIDE_INT rhsunitoffset, rhsoffset;

   if (offset == NULL_TREE || !host_integerp (offset, 0))
       rhsoffset = UNKNOWN_OFFSET;
   else {
       /* Make sure the bit-offset also fits.  */
       rhsunitoffset = TREE_INT_CST_LOW (offset);
       rhsoffset = rhsunitoffset * BITS_PER_UNIT;
       if (rhsunitoffset != rhsoffset / BITS_PER_UNIT)
	   rhsoffset = UNKNOWN_OFFSET;
   }

   cs_get_constraint_for_rhs (ptr, results, bb, cnode);
   if (rhsoffset == 0)
       return;

   /* As we are eventually appending to the solution do not use
      VEC_iterate here. */
   n = VEC_length (ce_s, *results);
   for (j = 0; j < n; j++) {
       csvarinfo_t curr;
       c = *VEC_index (ce_s, *results, j);
	
       curr = cs_get_varinfo (c.var);

       /* If this varinfo represents a full variable just use it. */
       if (c.type == ADDRESSOF && curr->is_full_var)
	{
	   c.offset = 0;
	   //c.ptr_arith = false; //For Pointer Arithmetic	
// 	   fprintf(dump_file,"\nPTR Arith2\n");
	}
       /* If we do not know the offset add all subfields. */
       else if (c.type == ADDRESSOF && rhsoffset == UNKNOWN_OFFSET) {
	   csvarinfo_t temp = cs_lookup_vi_for_tree (curr->decl);
	   do {
	       struct constraint_expr c2;
	       c2.var = temp->id;
	       c2.type = ADDRESSOF;
	       c2.offset = 0;
	       if (c2.var != c.var)
		{
	   	   //c2.ptr_arith = false; //For Pointer Arithmetic	
 //	   	   fprintf(dump_file,"\nPTR Arith3\n");
		   VEC_safe_push (ce_s, heap, *results, &c2);
		}
	       temp = temp->next;
	   } while (temp);
       }
       else if (c.type == ADDRESSOF) {
	   csvarinfo_t temp;
	   unsigned HOST_WIDE_INT offset = curr->offset + rhsoffset;

	   /* Search the sub-field which overlaps with the
	      pointed-to offset.  If the result is outside of the variable
	      we have to provide a conservative result, as the variable is
	      still reachable from the resulting pointer (even though it
	      technically cannot point to anything).  The last and first
	      sub-fields are such conservative results.
	      ???  If we always had a sub-field for &object + 1 then
	      we could represent this in a more precise way.  */
	   if (rhsoffset < 0 && curr->offset < offset)
	       offset = 0;
	   temp = cs_first_or_preceding_vi_for_offset (curr, offset);

	   /* If the found variable is not exactly at the pointed to
	     result, we have to include the next variable in the
	     solution as well.  Otherwise two increments by offset / 2
	     do not result in the same or a conservative superset
	     solution.  */
	   if (temp->offset != offset && temp->next != NULL) {
	       struct constraint_expr c2;
	       c2.var = temp->next->id;
	       c2.type = ADDRESSOF;
	       c2.offset = 0;
      	       //c2.ptr_arith = false; //For Pointer Arithmetic	
//	       fprintf(dump_file,"\nPTR Arith4\n");
	       VEC_safe_push (ce_s, heap, *results, &c2);
	   }
	   c.var = temp->id;
	   c.offset = 0;
  	   //c.ptr_arith = false; //For Pointer Arithmetic	
//           fprintf(dump_file,"\nPTR Arith5\n");
       }
       else
	{
	   c.offset = rhsoffset;
	   c.ptr_arith = true;
//           fprintf(dump_file,"\nPTR Arith6\n");
	}

       VEC_replace (ce_s, *results, j, &c);
   }
}

/* Given a COMPONENT_REF T, return the constraint_expr vector for it.
   If address_p is true the result will be taken its address of.
   If lhs_p is true then the constraint expression is assumed to be used
   as the lhs.  */

void cs_get_constraint_for_component_ref (tree t, VEC(ce_s, heap) **results,
				  bool address_p, bool lhs_p, basic_block bb, struct cgraph_node * cnode)
{
//	fprintf(dump_file,"\n In parser.cpp component ref\n");

   tree orig_t = t;
   HOST_WIDE_INT bitsize = -1;
   HOST_WIDE_INT bitmaxsize = -1;
   HOST_WIDE_INT bitpos;
   tree forzero;
   struct constraint_expr *result;

   /* Some people like to do cute things like take the address of
     &0->a.b */
   forzero = t;
   while (handled_component_p (forzero)
	 || INDIRECT_REF_P (forzero)
	 || TREE_CODE (forzero) == MEM_REF)
       forzero = TREE_OPERAND (forzero, 0);

   if (CONSTANT_CLASS_P (forzero) && integer_zerop (forzero)) {
       struct constraint_expr temp;
       temp.offset = 0;
       temp.var = readonly_id;
       temp.type = SCALAR;
       //temp.ptr_arith = false;	
       VEC_safe_push (ce_s, heap, *results, &temp);
       return;
   }

   /* Handle type-punning through unions. If we are extracting a pointer
      from a union via a possibly type-punning access that pointer
      points to anything, similar to a conversion of an integer to
      a pointer.  */
   if (!lhs_p) {
      tree u;
      for (u = t;
	   TREE_CODE (u) == COMPONENT_REF || TREE_CODE (u) == ARRAY_REF;
	   u = TREE_OPERAND (u, 0))
	if (TREE_CODE (u) == COMPONENT_REF
	    && TREE_CODE (TREE_TYPE (TREE_OPERAND (u, 0))) == UNION_TYPE) 
 	{
	/*
            struct constraint_expr temp;

            temp.offset = 0;
            temp.var = anything_id;
            temp.type = ADDRESSOF;
            VEC_safe_push (ce_s, heap, *results, &temp);
	*/
            return;
        }
   }

   t = get_ref_base_and_extent (t, &bitpos, &bitsize, &bitmaxsize);

   /* Pretend to take the address of the base, we'll take care of
      adding the required subset of sub-fields below.  */
   cs_get_constraint_for_1 (t, results, true, lhs_p, bb, cnode);
   if (VEC_length (ce_s, *results) == 0)
       return;
   else
       gcc_assert (VEC_length (ce_s, *results) == 1);
   
   result = VEC_last (ce_s, *results);
   //result->ptr_arith = false;

   if (result->type == SCALAR
       && cs_get_varinfo (result->var)->is_full_var)
       /* For single-field vars do not bother about the offset.  */
       result->offset = 0;
   else if (result->type == SCALAR) {
      /* In languages like C, you can access one past the end of an
	 array.  You aren't allowed to dereference it, so we can
	 ignore this constraint. When we handle pointer subtraction,
	 we may have to do something cute here.  */

      if ((unsigned HOST_WIDE_INT)bitpos < cs_get_varinfo (result->var)->fullsize
	  && bitmaxsize != 0) {
	  /* It's also not true that the constraint will actually start at the
	     right offset, it may start in some padding.  We only care about
	     setting the constraint to the first actual field it touches, so
	     walk to find it.  */
	  struct constraint_expr cexpr = *result;
	  csvarinfo_t curr;
	  VEC_pop (ce_s, *results);
	  cexpr.offset = 0;
	  for (curr = cs_get_varinfo (cexpr.var); curr; curr = curr->next) {
	      if (ranges_overlap_p (curr->offset, curr->size,
				    bitpos, bitmaxsize)) {
		  cexpr.var = curr->id;
		  //cexpr.ptr_arith = false;
		  VEC_safe_push (ce_s, heap, *results, &cexpr);
		  if (address_p)
		     break;
	       }
	   }
	   /* If we are going to take the address of this field then
	      to be able to compute reachability correctly add at least
	      the last field of the variable.  */
	   if (address_p && VEC_length (ce_s, *results) == 0) {
	       curr = cs_get_varinfo (cexpr.var);
	       while (curr->next)
		   curr = curr->next;
	       cexpr.var = curr->id;
	       //cexpr.ptr_arith = false;
	       VEC_safe_push (ce_s, heap, *results, &cexpr);
	   }
	   /*
	   else if (VEC_length (ce_s, *results) == 0)
            // Assert that we found *some* field there. The user couldn't be
            // accessing *only* padding.
            // Still the user could access one past the end of an array
            // embedded in a struct resulting in accessing *only* padding.
            // Or accessing only padding via type-punning to a type
            // that has a filed just in padding space.
            {
              cexpr.type = SCALAR;
              cexpr.var = anything_id;
              cexpr.offset = 0;
              VEC_safe_push (ce_s, heap, *results, &cexpr);
            }
	    */
       }
       else if (bitmaxsize == 0) {
	  if (dump_file && (dump_flags & TDF_DETAILS));
       }
       else
	  if (dump_file && (dump_flags & TDF_DETAILS));
   }
   else if (result->type == DEREF) {
      /* If we do not know exactly where the access goes say so.  Note
	 that only for non-structure accesses we know that we access
	 at most one subfiled of any variable.  */
       if (bitpos == -1 || bitsize != bitmaxsize
	  || AGGREGATE_TYPE_P (TREE_TYPE (orig_t))	/* Look into : Structure variables */
	  || result->offset == UNKNOWN_OFFSET)
	   result->offset = UNKNOWN_OFFSET;
       else
	   result->offset += bitpos;
   }
   else
       gcc_unreachable ();
}

/* Get a constraint expression vector from an SSA_VAR_P node.
   If address_p is true, the result will be taken its address of.  */

void cs_get_constraint_for_ssa_var (tree t, VEC(ce_s, heap) **results, bool address_p, basic_block bb, struct cgraph_node * cnode)
{

   struct constraint_expr cexpr;
   csvarinfo_t vi;

   /* We allow FUNCTION_DECLs here even though it doesn't make much sense. */
   gcc_assert (SSA_VAR_P (t) || DECL_P (t));


   /* For parameters, get at the points-to set for the actual parm decl. */
   if (TREE_CODE (t) == SSA_NAME
       && (TREE_CODE (SSA_NAME_VAR (t)) == PARM_DECL
 	  || TREE_CODE (SSA_NAME_VAR (t)) == RESULT_DECL)
       && SSA_NAME_IS_DEFAULT_DEF (t)) {
       cs_get_constraint_for_ssa_var (SSA_NAME_VAR (t), results, address_p, bb, cnode);

       return;
   }

   vi = cs_get_vi_for_tree (t, bb, cnode);
   cexpr.var = vi->id;

   cexpr.type = SCALAR;
   //cexpr.ptr_arith = false;	
   cexpr.offset = 0;

   /* If we are not taking the address of the constraint expr, add all
      sub-fiels of the variable as well.  */
/*
   if (!address_p)
   if (!vi->is_full_var)
   else
*/

   if (!address_p && !vi->is_full_var) {
      for (; vi; vi = vi->next) {
	   cexpr.var = vi->id;
	  

	   VEC_safe_push (ce_s, heap, *results, &cexpr);
      }
      return;
   }

   VEC_safe_push (ce_s, heap, *results, &cexpr);
}

/* Given a tree T, return the constraint expression for it.  */

void cs_get_constraint_for_1 (tree t, VEC (ce_s, heap) **results, bool address_p,
		      bool lhs_p, basic_block bb, struct cgraph_node * cnode)
{
   struct constraint_expr temp;

   /* x = integer is all glommed to a single variable, which doesn't
     point to anything by itself.  That is, of course, unless it is an
     integer constant being treated as a pointer, in which case, we
     will return that this is really the addressof anything.  This
     happens below, since it will fall into the default case. The only
     case we know something about an integer treated like a pointer is
     when it is the NULL pointer, and then we just say it points to
     NULL.

     Do not do that if -fno-delete-null-pointer-checks though, because
     in that case *NULL does not fail, so it _should_ alias *anything.
     It is not worth adding a new option or renaming the existing one,
     since this case is relatively obscure.  */
   if ((TREE_CODE (t) == INTEGER_CST && integer_zerop (t))
      /* The only valid CONSTRUCTORs in gimple with pointer typed
	 elements are zero-initializer.  But in IPA mode we also
	 process global initializers, so verify at least.  */
      || (TREE_CODE (t) == CONSTRUCTOR
	  && CONSTRUCTOR_NELTS (t) == 0)) {
       if (flag_delete_null_pointer_checks) {
	   temp.var = nothing_id;
           temp.type = ADDRESSOF;
           temp.offset = 0;
	   //temp.ptr_arith = false;	

           VEC_safe_push (ce_s, heap, *results, &temp);
       }
       return;
   }

  /* String constants are read-only. Don't consider them. 
   if (TREE_CODE (t) == STRING_CST)
       return;*/

   /* String constants are read-only. */
   if (TREE_CODE (t) == STRING_CST) {
      temp.var = readonly_id;
      temp.type = SCALAR;
      temp.offset = 0;
      //temp.ptr_arith = false;
      VEC_safe_push (ce_s, heap, *results, &temp);
      return;
   }

   switch (TREE_CODE_CLASS (TREE_CODE (t))) {
       case tcc_expression:
       {
           switch (TREE_CODE (t)) {
	       case ADDR_EXPR:

	           cs_get_constraint_for_address_of (TREE_OPERAND (t, 0), results, bb, cnode);
           return;
	        default:;
	   }
 	   break;
       }
       case tcc_reference:
       {
	   switch (TREE_CODE (t)) {
	       case MEM_REF:
	       {
	           struct constraint_expr cs;
	      	   csvarinfo_t vi, curr;
	           tree off = double_int_to_tree (sizetype, mem_ref_offset (t));
	      	   cs_get_constraint_for_ptr_offset (TREE_OPERAND (t, 0), off, results, bb, cnode);
                   if (VEC_length (ce_s, *results) == 0)
                       return;
	      	   cs_do_deref (results, bb, cnode);

	           /* If we are not taking the address then make sure to process
		      all subvariables we might access.  */
	      	   cs = *VEC_last (ce_s, *results);
                   //cs.ptr_arith = false;
	      	   if (address_p || cs.type != SCALAR)
		       return;

	      	   vi = cs_get_varinfo (cs.var);
	      	   curr = vi->next;
	      	   if (!vi->is_full_var && curr) {
		       unsigned HOST_WIDE_INT size;
		       if (host_integerp (TYPE_SIZE (TREE_TYPE (t)), 1))
		           size = TREE_INT_CST_LOW (TYPE_SIZE (TREE_TYPE (t)));
		       else
		           size = -1;
		       for (; curr; curr = curr->next) {
		      	   if (curr->offset - vi->offset < size) {
			       cs.var = curr->id;
			       VEC_safe_push (ce_s, heap, *results, &cs);
			   }
		           else
			       break;
		       }
		   }
	           return;
	       }
	       case ARRAY_REF:
	       case ARRAY_RANGE_REF:
	       case COMPONENT_REF:
	           cs_get_constraint_for_component_ref (t, results, address_p, lhs_p, bb, cnode);
	           return;
	       case VIEW_CONVERT_EXPR:
	           cs_get_constraint_for_1 (TREE_OPERAND (t, 0), results, address_p, lhs_p, bb, cnode);
	    	   return;
	       /* We are missing handling for TARGET_MEM_REF here.  */
	       default:;
	   }
	   break;
       }
       case tcc_exceptional:
       {
	   switch (TREE_CODE (t)) {
	       case SSA_NAME:
	       {
		   cs_get_constraint_for_ssa_var (t, results, address_p, bb, cnode);
	           return;
	       }
	       case CONSTRUCTOR:
	       {
	           unsigned int i;
	      	   tree val;
	      	   VEC (ce_s, heap) *tmp = NULL;
	      	   FOR_EACH_CONSTRUCTOR_VALUE (CONSTRUCTOR_ELTS (t), i, val) {
		       struct constraint_expr *rhsp;
		       unsigned j;
		       cs_get_constraint_for_1 (val, &tmp, address_p, lhs_p, bb, cnode);
		       FOR_EACH_VEC_ELT (ce_s, tmp, j, rhsp)
		           VEC_safe_push (ce_s, heap, *results, rhsp);
		       VEC_truncate (ce_s, tmp, 0);
		   }
	           VEC_free (ce_s, heap, tmp);
	           /* We do not know whether the constructor was complete,
	              so technically we have to add &NOTHinG or &ANYTHinG
		      like we do for an empty constructor as well.  */
	           return;
	       }
	       default:;
	   }
	   break;
       }
       case tcc_declaration:
       {
	   cs_get_constraint_for_ssa_var (t, results, address_p, bb, cnode);
	   return;
       }
       case tcc_constant:
	   return;
       default:;
   }
}

/* Efficiently generates constraints from all entries in *RHSC to all
   entries in *LHSC.  */

void cs_process_all_all_constraints (VEC (ce_s, heap) *lhsc, VEC (ce_s, heap) *rhsc, basic_block bb)
{
   struct constraint_expr *lhsp, *rhsp;
   unsigned i, j;

//   print_variable_data ();

   FOR_EACH_VEC_ELT (ce_s, lhsc, i, lhsp) {
       FOR_EACH_VEC_ELT (ce_s, rhsc, j, rhsp) {
//	   print_variable_data (lhsp->var);
//	   print_variable_data (rhsp->var);
           cs_process_constraint (new_constraint (*lhsp, *rhsp), bb);
           multi_rhs = true;
       }
       multi_rhs = false;
   }
}


/* Given a tree T, return the constraint expression for taking the
   address of it. */

void cs_get_constraint_for_address_of (tree t, VEC (ce_s, heap) **results, basic_block bb, struct cgraph_node * cnode)
{
   struct constraint_expr *c;
   unsigned int i;

   cs_get_constraint_for_1 (t, results, true, true, bb, cnode);
   FOR_EACH_VEC_ELT (ce_s, *results, i, c) {
       if (c->type == DEREF)
           c->type = SCALAR;
       else
           c->type = ADDRESSOF;
       //c->ptr_arith = false;
   }
}

/* Given a gimple tree T, return the constraint expression vector for it.  */

void cs_get_constraint_for (tree t, VEC (ce_s, heap) **results, basic_block bb, struct cgraph_node * cnode)
{
  gcc_assert (VEC_length (ce_s, *results) == 0);
  cs_get_constraint_for_1 (t, results, false, true, bb, cnode);
}


/* Creation function node for DECL, using NAME, and return the index
   of the variable we've created for the function.  */

csvarinfo_t cs_create_func_info_for (tree decl, const char *name, struct cgraph_node * cnode)
{
   csvarinfo_t vi, prev_vi;
   tree arg;
   unsigned int i;
   bool is_varargs = false;
   unsigned int num_args = count_num_arguments (decl, &is_varargs);
   /* Create the variable info.  */
   vi = cs_new_var_info (decl, name, cnode);
   vi->offset = 0;
   vi->size = 1;
   vi->fullsize = num_args + 1;
   vi->may_have_pointers = false;
   if (is_varargs)
       vi->fullsize = ~0;
   cs_insert_vi_for_tree (vi->decl, vi);

   prev_vi = vi;

   /* Set up variables for each argument.  */
   arg = DECL_ARGUMENTS (decl);
   for (i = 1; i < num_args + 1; i++) {
       csvarinfo_t argvi;
       tree argdecl = decl;

       if (arg)
           argdecl = arg;

       argvi = cs_new_var_info (argdecl, alias_get_name (argdecl), cnode);
       create_cdv(argvi);
       unsigned int t = argvi->id;	
       ((function_info *)(cnode->aux))->add_param(t);
       argvi->offset = i;
       argvi->size = 1;
       argvi->is_full_var = true;
       argvi->fullsize = vi->fullsize;
       if (arg)
       gcc_assert (prev_vi->offset < argvi->offset);
       prev_vi->next = argvi;
       prev_vi = argvi;
       if (arg) {
           cs_insert_vi_for_tree (arg, argvi);
           arg = DECL_CHAIN (arg);
       }
   }

   /* Add one representative for all further args.  */
   if (is_varargs) {
       csvarinfo_t argvi;
       const char *newname;
       char *tempname;
       tree decl;

       asprintf (&tempname, "%s.varargs", name);
       newname = ggc_strdup (tempname);
       free (tempname);

       /* CHANGE DUE TO GCC-4.7.2 */
       /* We need sth that can be pointed to for va_start.  */
       decl = build_fake_var_decl (ptr_type_node);

       /* According to gcc-4.6.*
       decl = create_tmp_var_raw (ptr_type_node, name);
       get_var_ann (decl); */

       argvi = cs_new_var_info (decl, newname, cnode);
       argvi->offset = 1 + num_args;
       argvi->size = ~0;
       argvi->is_full_var = true;
       argvi->is_heap_var = true;
       argvi->fullsize = vi->fullsize;
       gcc_assert (prev_vi->offset < argvi->offset);
       prev_vi->next = argvi;
       prev_vi = argvi;
   }

   return vi;
}

/* Find the first varinfo in the same variable as START that overlaps with
   OFFSET.  Return NULL if we can't find one.  */

csvarinfo_t cs_first_vi_for_offset (csvarinfo_t start, unsigned HOST_WIDE_INT offset)       /* Look into */
{
   offset += start->offset;

   /* If the offset is outside of the variable, bail out.  */
   if (offset >= start->fullsize)
       return NULL;

   /* If we cannot reach offset from start, lookup the first field
      and start from there.  */
   if (start->offset > offset)
       start = cs_lookup_vi_for_tree (start->decl);

   while (start) {
      /* We may not find a variable in the field list with the actual
         offset when when we have glommed a structure to a variable.
         In that case, however, offset should still be within the size
         of the variable. */
       if (offset >= start->offset
           && (offset - start->offset) < start->size)
           return start;

       start= start->next;
   }

   return NULL;
}

/* Handle aggregate copies by expanding into copies of the respective
   fields of the structures.  */

void cs_do_structure_copy (tree lhsop, tree rhsop, basic_block bb, struct cgraph_node * cnode)  /* Look into : Structure variables */
{
   struct constraint_expr *lhsp, *rhsp;
   VEC (ce_s, heap) *lhsc = NULL, *rhsc = NULL;
   unsigned j;

   cs_get_constraint_for (lhsop, &lhsc, bb, cnode);
   cs_get_constraint_for_rhs (rhsop, &rhsc, bb, cnode);

   lhsp = VEC_index (ce_s, lhsc, 0);
   rhsp = VEC_index (ce_s, rhsc, 0);


   // Commented by Vini, used by Prashant
//    if (lhsp->type == DEREF)
//       return;
//    if (rhsp->type == DEREF) {
//        gcc_assert (VEC_length (ce_s, rhsc) == 1);
//        rhsp->var = undef_id;
//        rhsp->offset = 0;
//        rhsp->type = ADDRESSOF;
//        cs_process_all_all_constraints (lhsc, rhsc, bb);
//    }

   // Added by Vini
   if (lhsp->type == DEREF || rhsp->type == DEREF)
   {
     if (lhsp->type == DEREF)
       {
         gcc_assert (VEC_length (ce_s, lhsc) == 1);
         lhsp->offset = UNKNOWN_OFFSET;
       }
     if (rhsp->type == DEREF)
       {
         gcc_assert (VEC_length (ce_s, rhsc) == 1);
         rhsp->offset = UNKNOWN_OFFSET;
       }
     cs_process_all_all_constraints (lhsc, rhsc, bb);
   }

   else if (lhsp->type == SCALAR &&
            (rhsp->type == SCALAR || rhsp->type == ADDRESSOF)) {
       HOST_WIDE_INT lhssize, lhsmaxsize, lhsoffset;
       HOST_WIDE_INT rhssize, rhsmaxsize, rhsoffset;
       unsigned k = 0;
       get_ref_base_and_extent (lhsop, &lhsoffset, &lhssize, &lhsmaxsize);
       get_ref_base_and_extent (rhsop, &rhsoffset, &rhssize, &rhsmaxsize);
       for (j = 0; VEC_iterate (ce_s, lhsc, j, lhsp);) {
           csvarinfo_t lhsv, rhsv;
           rhsp = VEC_index (ce_s, rhsc, k);
           lhsv = cs_get_varinfo (lhsp->var);
           rhsv = cs_get_varinfo (rhsp->var);
          if (lhsv->may_have_pointers
               && (lhsv->is_full_var
                  || rhsv->is_full_var
                  || ranges_overlap_p (lhsv->offset + rhsoffset, lhsv->size,
                                       rhsv->offset + lhsoffset, rhsv->size)))
	   {
               cs_process_constraint (new_constraint (*lhsp, *rhsp), bb);
	   }
           if (!rhsv->is_full_var && (lhsv->is_full_var
                  || (lhsv->offset + rhsoffset + lhsv->size
                      > rhsv->offset + lhsoffset + rhsv->size))) {
               ++k;
               if (k >= VEC_length (ce_s, rhsc))
                   break;
           }
           else
	   {
               ++j;
           }
       }
   }
   else
   {
       gcc_unreachable ();
   }


   VEC_free (ce_s, heap, lhsc);
   VEC_free (ce_s, heap, rhsc);
}

void cs_init_base_vars (struct cgraph_node * cnode)
{
  // csvarinfo_t var_nothing, var_integer, var_undef;
 csvarinfo_t var_nothing, var_readonly, var_escaped, var_undef;

   /* Create an UNKNOWN variable, for unknown pointer values. */
   var_undef = cs_new_var_info (NULL_TREE, "undef", cnode);
   gcc_assert (var_undef->id == undef_id);
//   gcc_assert (var_undef->name == "undef");
   var_undef->offset = 0;
   var_undef->size = ~0;
   var_undef->fullsize = ~0;
   var_undef->next = NULL;

   /* Create the NULL variable, used to represent that a variable points
      to NULL.  */
   var_nothing = cs_new_var_info (NULL_TREE, "null", cnode);
   gcc_assert (var_nothing->id == nothing_id);
//   gcc_assert (var_nothing->name == "null");
   var_nothing->offset = 0;
   var_nothing->size = ~0;
   var_nothing->fullsize = ~0;

   /* Create the INTEGER variable, used to represent that a variable points
     to what an INTEGER "points to".  
   var_integer = cs_new_var_info (NULL_TREE, "integer", cnode);
   gcc_assert (var_integer->id == integer_id);
   var_integer->size = ~0;
   var_integer->fullsize = ~0;
   var_integer->offset = 0;
   var_integer->next = NULL;*/

   /* Create an ESCAPED variable, for escaped pointer values. */
   var_escaped = cs_new_var_info (NULL_TREE, "escaped", cnode);
   gcc_assert (var_escaped->id == escaped_id);
//   gcc_assert (var_escaped->name == "escaped");
   var_escaped->offset = 0;
   var_escaped->size = ~0;
   var_escaped->fullsize = ~0;
   var_escaped->next = NULL;

   /* Create the READONLY variable, used to represent string constants
      and integer pointers. */
   var_readonly = cs_new_var_info (NULL_TREE, "readonly", cnode);
   gcc_assert (var_readonly->id == readonly_id);
//   gcc_assert (var_readonly->name == "readonly");
   var_readonly->size = ~0;
   var_readonly->fullsize = ~0;
   var_readonly->offset = 0;
   var_readonly->next = NULL;

}

void cs_init_alias_vars (struct cgraph_node * cnode)
{
   csvarmap = VEC_alloc (csvarinfo_t, heap, 200);
   aliases = VEC_alloc (constraint_t, heap, 200);
   constraint_pool = create_alloc_pool ("Constraint pool", sizeof (struct constraint), 200);
   csvarinfo_pool = create_alloc_pool ("Variable pool", sizeof (struct csvariable_info), 200);
   vi_for_tree = pointer_map_create ();
   cs_init_base_vars (cnode);
   gcc_obstack_init (&fake_var_decl_obstack);
}

tree cs_get_var (tree t)
{
   if (TREE_CODE (t) == MEM_REF) {
       t = TREE_OPERAND (t, 0);
       return cs_get_var (t);
   }
   return t;
}


/*-------------------------------------------------------------------------------------
  Function which processes the constraint t, retrieves the lhs and rhs of the pointsto
  constraint, and updates the alias pool. 
  ------------------------------------------------------------------------------------*/

void cs_process_constraint (constraint_t t, basic_block bb)
{
   struct constraint_expr rhs = t->rhs;
   struct constraint_expr lhs = t->lhs;

   gcc_assert (rhs.var < VEC_length (csvarinfo_t, csvarmap));
   gcc_assert (lhs.var < VEC_length (csvarinfo_t, csvarmap));

   if (!is_proper_var (lhs.var))
   {
       return;
   }

   // ADDRESSOF on the lhs is invalid.  
   gcc_assert (lhs.type != ADDRESSOF);

   if (check_deref) 
       deref_stmt = (rhs.type == DEREF || lhs.type == DEREF);

   // if (!compute_only_pinfo)
       insert_alias_in_pool (t, cs_get_varinfo (lhs.var), bb);

 /*  if (compute_alias_and_pinfo)
	{
       //compute_stmt_out_1 (cpinfo, t);
	}
   
   if (compute_only_pinfo)
	{
       //compute_stmt_out_2 (cpinfo, t);
	}*/
}

bool possibly_deref (gimple stmt)
{
   tree lhsop = gimple_assign_lhs (stmt);
   tree rhsop = (gimple_num_ops (stmt) == 2) ? gimple_assign_rhs1 (stmt) : NULL;

   //return ((TREE_CODE (lhsop) == MEM_REF) ||
   //		(rhsop && TREE_CODE (rhsop) == MEM_REF));

   return ((TREE_CODE (lhsop) == MEM_REF) ||
   		(rhsop && TREE_CODE (rhsop) == MEM_REF) ||
   		(TREE_CODE (lhsop) == COMPONENT_REF) ||
   		(rhsop && TREE_CODE (rhsop) == COMPONENT_REF));

}


/* --------------------------------------------------------------------
   Perform necessary initializations for the callstrings pointsto pass.
   -------------------------------------------------------------------*/

/*--------------------------------------------------------------------
  Returns the called function's decl tree. If it is a direct function 
  call, the TREE_CODE of the returned decl will be FUNCTION_DECL. If 
  it is a call via function pointer, it will be VAR_DECL. 
  -------------------------------------------------------------------*/

tree get_called_fn_decl (gimple stmt)
{
    /* If we can resolve it here, its a simple function call. */
    tree decl = gimple_call_fndecl (stmt);
    /* The call is through function pointer. */
    if (!decl)
        decl = gimple_call_fn (stmt);
    return decl;
}

// Vini, June'15
void map_return_value (struct cgraph_node * src_function, 
	basic_block call_block,
	basic_block callee_end_block, 
	struct cgraph_node * called_function)
{
   bool found_rhs = true;
   /* Is there a receiving pointer value in the call statement? */
   gimple call_stmt = bb_call_stmt (call_block);
   if (is_gimple_call (call_stmt)) 
   {
      tree lhsop = gimple_call_lhs (call_stmt);
      if (lhsop && field_must_have_pointers (lhsop)) 
      {
         found_rhs = false;
         gimple_stmt_iterator ret_gsi;
         for (ret_gsi = gsi_start_bb (callee_end_block); !gsi_end_p (ret_gsi); gsi_next (&ret_gsi)) 
         {
            gimple ret_stmt = gsi_stmt (ret_gsi);
            if (gimple_code (ret_stmt) == GIMPLE_RETURN)
            {
               tree rhsop = gimple_return_retval (ret_stmt);
	       if (rhsop != NULL_TREE)
               {
                  /* Map it to the return value of return statement. */
                  VEC(ce_s, heap) *lhsc = NULL, *rhsc = NULL;
                  cs_get_constraint_for (lhsop, &lhsc, call_block, src_function);
                  cs_get_constraint_for (rhsop, &rhsc, callee_end_block, called_function);
                  cs_process_all_all_constraints (lhsc, rhsc, call_block);
                  VEC_free (ce_s, heap, lhsc);
                  VEC_free (ce_s, heap, rhsc);

		  found_rhs = true;
                  break;
               }
	    }
         }
      }
   }

//   if (!found_rhs)
//   {
//	print_gimple_stmt (dump_file, call_stmt, 0, 0);
	// This need not be an error since a function pointer might be wrongly pointing to a function
//	fprintf (dump_file, "\ncall-statement expects return, but return-block of function %s not found",
//		cgraph_node_name (called_function));
//   }
}

// Vini, June'15
void map_function_arguments (struct cgraph_node * src_function, 
	basic_block call_block, 
	gimple call_stmt, 
	struct cgraph_node * called_function)
{
   //fprintf (dump_file, "\nmap_function_arguments()");
   //fprintf (dump_file, "\nsrc_function=%s", cgraph_node_name (src_function));
   //fprintf (dump_file, "\ncalled_function=%s", cgraph_node_name (called_function));
   //fprintf (dump_file, "\n");
   //print_gimple_stmt (dump_file, call_stmt, 0, 0);

   VEC(ce_s, heap) *rhsc = NULL;
   size_t j;
   int argoffset = 1;
   csvarinfo_t fi;

   unsigned int num = 0;
   for (tree t = DECL_ARGUMENTS (called_function->decl); t; t = DECL_CHAIN (t))
        ++num;
   if (num != gimple_call_num_args (call_stmt))
   {
        VEC_free (ce_s, heap, rhsc);
	return;
   }

   fi = cs_get_vi_for_tree (called_function->decl, call_block, src_function);

   for (j = 0; j < gimple_call_num_args (call_stmt); j++) {
       //fprintf (dump_file, "\narg=%d", j);
       struct constraint_expr lhs ;
       struct constraint_expr *rhsp;
       tree arg = gimple_call_arg (call_stmt, j);
       if (field_must_have_pointers (arg)) {
           //fprintf (dump_file, "\narg has pointers");
           cs_get_constraint_for (arg, &rhsc, call_block, src_function);
	   //fprintf (dump_file, "\nFetched arg in rhsc");
           lhs.type = SCALAR;
           csvarinfo_t param = cs_first_vi_for_offset (fi, argoffset);
	   if (!param)
           {
                VEC_free (ce_s, heap, rhsc);
		return;
           }
           lhs.var = param->id;
           lhs.offset = 0;
	   //fprintf (dump_file, "\nmapped arguments:");
   	   //fprintf (dump_file, "\nlhs var %d, type %d", lhs.var, lhs.type);
           while (VEC_length (ce_s, rhsc) != 0) {
               rhsp = VEC_last (ce_s, rhsc);
	       //fprintf (dump_file, "\nrhs var %d, type %d", rhsp->var, rhsp->type);
               cs_process_constraint (new_constraint (lhs, *rhsp), call_block);
               //fprintf (dump_file, "\nlhs rhs constraint created");
               VEC_pop (ce_s, rhsc);
               multi_rhs = true;
           }
          multi_rhs = false;
       }
       argoffset++;
   }
   VEC_free (ce_s, heap, rhsc);

   //fprintf (dump_file, "\nDone map_function_arguments");
}


void map_arguments_at_call (gimple stmt, tree decl, bool generate_liveness, basic_block bb, struct cgraph_node * cnode)
{

   VEC(ce_s, heap) *rhsc = NULL;
   size_t j;
   int argoffset = 1;
   csvarinfo_t fi;

   /* Generate liveness for call via function pointers and library routines. */
   if (generate_liveness) {

       struct constraint_expr *exp;
       unsigned i;

       for (j = 0; j < gimple_call_num_args (stmt); j++) {

           tree arg = gimple_call_arg (stmt, j);
		if(AGGREGATE_TYPE_P (TREE_TYPE (arg)))
//		       fprintf(dump_file,"\nArgument in library call\n");
           if (field_must_have_pointers (arg) && TREE_CODE (arg) != ADDR_EXPR) {
//	       fprintf(dump_file,"\nArgument is a pointer\n");
               VEC (ce_s, heap) *results = NULL;
               cs_get_constraint_for (arg, &results, bb, cnode);
               FOR_EACH_VEC_ELT (ce_s, results, i, exp)
	       {
//                   ((block_information *)(bb->aux))->add_to_parsed_data_indices (exp->var, false, bb);	// generate_liveness_constraints // Vini: Why commented out???
		     generate_liveness_constraint(bb,exp->var);  // To Be Checked
	       }
               VEC_free (ce_s, heap, results);
           }
       }
       return;
   }

   /* Map call arguments. */
   fi = cs_get_vi_for_tree (decl, bb, cnode);

   for (j = 0; j < gimple_call_num_args (stmt); j++) {

//       ((function_info *)(cnode->aux))->cons_num++;

       struct constraint_expr lhs ;
       struct constraint_expr *rhsp;
       tree arg = gimple_call_arg (stmt, j);
       if (field_must_have_pointers (arg)) {
           cs_get_constraint_for (arg, &rhsc, bb, cnode);
           lhs.type = SCALAR;
           lhs.var = cs_first_vi_for_offset (fi, argoffset)->id;
           lhs.offset = 0;
           while (VEC_length (ce_s, rhsc) != 0) {
               rhsp = VEC_last (ce_s, rhsc);
              cs_process_constraint (new_constraint (lhs, *rhsp), bb);
               VEC_pop (ce_s, rhsc);
               multi_rhs = true;
           }
          multi_rhs = false;
       }
       argoffset++;
   }
   VEC_free (ce_s, heap, rhsc);

}

void process_library_call (gimple stmt, basic_block bb, struct cgraph_node * cnode)
{

   /* Generate liveness. */
   map_arguments_at_call (stmt, NULL, true, bb, cnode);
   /* Handle malloc by introducing a points to to heap. */
   if (gimple_call_flags (stmt) & ECF_MALLOC) {
       tree lhs = gimple_call_lhs (stmt);
       if (lhs && field_must_have_pointers (lhs))
	{	
           cs_make_constraint_from_heapvar (cs_get_vi_for_tree (lhs, bb, cnode), "heap", bb, cnode);
	    constraint_t con = VEC_pop(constraint_t,aliases);
	    con->heap_alloc = true;
            VEC_safe_push (constraint_t, heap, aliases, con);	
	}
   }
}

void generate_liveness_constraint(basic_block bb, unsigned int id)
{
((block_information *)(bb->aux))->get_list().push(id,false);

//((function_info *)(cnode->aux))->push_front(bb,1);

}


void process_gimple_assign_stmt (gimple stmt, basic_block bb, struct cgraph_node * cnode)
{

 tree lhsop = gimple_assign_lhs (stmt);
 tree rhsop = (gimple_num_ops (stmt) == 2) ? gimple_assign_rhs1 (stmt) : NULL;

   if (rhsop && TREE_CLOBBER_P (rhsop))
	return;


   if (field_must_have_pointers (lhsop)) 
   {
       VEC(ce_s, heap) *lhsc = NULL;
       VEC(ce_s, heap) *rhsc = NULL;
       if (rhsop && AGGREGATE_TYPE_P (TREE_TYPE (lhsop)))  /* Look into : Structure variables */
       {
		cs_do_structure_copy (lhsop, rhsop, bb, cnode); 
       }
       else 
       {
           cs_get_constraint_for (lhsop, &lhsc, bb, cnode);
           if (gimple_assign_rhs_code (stmt) == POINTER_PLUS_EXPR)
	   {
//		fprintf(dump_file,"\nPTR Arith1\n");
                cs_get_constraint_for_ptr_offset (gimple_assign_rhs1 (stmt),
                                           gimple_assign_rhs2 (stmt), &rhsc, bb, cnode);
	   }
           //else if (code == BIT_AND_EXPR
           //        && TREE_CODE (gimple_assign_rhs2 (t)) == INTEGER_CST)
           //{
              // Aligning a pointer via a BIT_AND_EXPR is offsetting
              //   the pointer.  Handle it by offsetting it by UNKNOWN.
           //   get_constraint_for_ptr_offset (gimple_assign_rhs1 (t), NULL_TREE, &rhsc);
           //}
           else if ((CONVERT_EXPR_CODE_P (gimple_assign_rhs_code (stmt))
                     && !(POINTER_TYPE_P (gimple_expr_type (stmt))
                     && !POINTER_TYPE_P (TREE_TYPE (rhsop))))
                     || gimple_assign_single_p (stmt))
	   {

                // cs_get_constraint_for (rhsop, &rhsc, bb, cnode);	// by Prashant
                cs_get_constraint_for_rhs (rhsop, &rhsc, bb, cnode);   // To Be Checked
//                cs_get_constraint_for (rhsop, &rhsc, bb, cnode);
	   }
	  // cs_process_all_all_constraints calls
	  // cs_process_constraint calls
	  // insert_alias_in_pool. This function stores constraints in a global
	  // variable: aliases (of type constraint_t).

          cs_process_all_all_constraints (lhsc, rhsc, bb);
       }

       // Commented by Prashant
       // If there is a store to a global variable the rhs escapes.
       // ...

       VEC_free (ce_s, heap, rhsc);
       VEC_free (ce_s, heap, lhsc);

//	print_assignment_data ();
   }

//   else
//   {
       // Generate liveness of lhs
       if (lhsop && TREE_CODE (lhsop) == MEM_REF)
       {
            // generate_liveness_constraint
		generate_liveness_constraint (bb, (cs_get_vi_for_tree (cs_get_var (lhsop), bb, cnode))->id);
       }
       
       // Generate liveness of rhs
       if (rhsop && TREE_CODE (rhsop) == MEM_REF)
       {
            // generate_liveness_constraint
		generate_liveness_constraint (bb, (cs_get_vi_for_tree (cs_get_var (rhsop), bb, cnode))->id);
       }
//   }
}


void append_to_bb_constraints (unsigned int id,bool b, basic_block bb)
{
((block_information *)(bb->aux))->get_list().push(id,b);
}

/*-------------------------------------------------------------------------
  Insert the constraint t in the alias pool. Update the alias list for the
  current basic block. Also, update the bb_alias_list of variable vi (forming 
  the LHS of the constraint) to reflect the fact that variable vi is the
  lhs of some constraint t.
  ------------------------------------------------------------------------*/
void insert_alias_in_pool (constraint_t t, csvarinfo_t vi, basic_block bb)
{

    // df_list new_alias;					// Vini: Why commented out? Liveness set
     unsigned int loc;
     bool alias_found = false;// check_alias_inclusion (t, vi, &loc);	// Vini: Why commented out?
     if (!alias_found) {
         loc = VEC_length (constraint_t, aliases);
         VEC_safe_push (constraint_t, heap, aliases, t);
         //append_constraint_to_varinfo (vi, loc);		// Vini: Why commented out? Adds to liveness set
     }
     //new_alias = create_df_constraint (loc);			// Vini: Why commented out? Adds to liveness set
     // if (!compute_alias_and_pinfo)
     {
//        ((block_information *)(bb->aux))->add_to_parsed_data_indices (loc, true, bb);	// Add to constraints (or parsed data) of the block
//	  generate_liveness_constraint(bb, loc);
	  append_to_bb_constraints (loc, true, bb);
     }
     //else							// Vini: Why commented out?
//     {
         //append_to_fptr_constraints (new_alias);		// Vini: Why commented out?
//     }
}

/*
void init_bb_aux(basic_block bb)
{
	
struct cgraph_node *cnode;

for (cnode=cgraph_nodes; cnode; cnode=cnode->next) {

        if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
          continue;
        push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

        FOR_EACH_BB(bb)
                {
                bb->aux = new block_information(cnode);
                }
        pop_cfun();
        }

}

void end_bb_aux(basic_block bb)
{

struct cgraph_node *cnode;

for (cnode=cgraph_nodes; cnode; cnode=cnode->next) {

if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
        continue;
        push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

        FOR_EACH_BB (bb) {
                if (bb->aux)
                        {
                        delete (block_information *)bb->aux;
                        bb->aux = NULL;
                        }
                }

        pop_cfun();
        }
}
*/

void process_gimple_condition(gimple stmt, basic_block bb, struct cgraph_node * cnode)
{
 struct constraint_expr *exp;
   unsigned i;

   tree op0 = gimple_cond_lhs (stmt);
   tree op1 = gimple_cond_rhs (stmt);

   if (field_must_have_pointers (op0) && TREE_CODE (op0) != ADDR_EXPR) {
       VEC (ce_s, heap) *results = NULL;
       cs_get_constraint_for (op0, &results, bb, cnode);
       FOR_EACH_VEC_ELT (ce_s, results, i, exp)
		generate_liveness_constraint (bb, exp->var);
       VEC_free (ce_s, heap, results);
   }
   if (field_must_have_pointers (op1) && TREE_CODE (op1) != ADDR_EXPR) {
       VEC (ce_s, heap) *results = NULL;
       cs_get_constraint_for (op1, &results, bb, cnode);
       FOR_EACH_VEC_ELT (ce_s, results, i, exp)
		generate_liveness_constraint (bb, exp->var);
       VEC_free (ce_s, heap, results);
   }

}

void process_gimple_phi_stmt (gimple stmt, basic_block bb, struct cgraph_node * cnode)
{
   VEC(ce_s, heap) *lhsc = NULL;
   VEC(ce_s, heap) *rhsc = NULL;
   struct constraint_expr *c;
   size_t i;
   unsigned int j;
//        print_gimple_stmt(dump_file,stmt,0,0);

   /* For a phi node, assign all the arguments to the result. */
   cs_get_constraint_for (gimple_phi_result (stmt), &lhsc, bb, cnode);
   for (i = 0; i < gimple_phi_num_args (stmt); i++) {
       tree strippedrhs = PHI_ARG_DEF (stmt, i);
       STRIP_NOPS (strippedrhs);
       cs_get_constraint_for (strippedrhs, &rhsc, bb, cnode);
       for (j = 0; VEC_iterate (ce_s, lhsc, j, c); j++) {
           struct constraint_expr *c2;
           while (VEC_length (ce_s, rhsc) > 0) {
               c2 = VEC_last (ce_s, rhsc);
               cs_process_constraint (new_constraint (*c, *c2), bb);
               VEC_pop (ce_s, rhsc);
               multi_rhs = true;
           }
       }
   }

   multi_rhs = false;
   VEC_free (ce_s, heap, rhsc);
   VEC_free (ce_s, heap, lhsc);
}

bool is_gimple_endblock (gimple t)
{
   return (gimple_code (t) == GIMPLE_RETURN);
}


/* Iterate over all the PHI nodes of the basic block and 
   calculate alias info for them. */

bool process_phi_pointers (basic_block bb, struct cgraph_node * cnode)
{
   gimple_stmt_iterator gsi;

   bool has_phi = false;
   for (gsi = gsi_start_phis (bb); !gsi_end_p (gsi); gsi_next (&gsi)) {
//       print_gimple_stmt (dump_file, gsi_stmt(gsi), 0,0);
       gimple phi = gsi_stmt (gsi);
       tree phi_result = gimple_phi_result (phi);
       if (is_gimple_reg (phi_result)) {
           if (field_must_have_pointers (phi_result)) {
               has_phi = true;
               process_gimple_phi_stmt (phi, bb, cnode);
           }
       }
   }
   return has_phi;
}

void generate_retval_liveness (gimple stmt, basic_block bb, struct cgraph_node * cnode)
{
   tree retval = gimple_return_retval (stmt);

   if (retval!=NULL_TREE && field_must_have_pointers (retval)) {
       VEC(ce_s, heap) *rhsc = NULL;
       struct constraint_expr *rhs;
       unsigned int i;

       cs_get_constraint_for (retval, &rhsc, bb, cnode);
       FOR_EACH_VEC_ELT (ce_s, rhsc, i, rhs)
	{
		generate_liveness_constraint (bb, rhs->var);
//		((function_info *)(cnode->aux))->add_ele_param_ret(rhs->var); 	
//		fprintf(dump_file,"\nReturn Type\n");
		((function_info *)(cnode->aux))->set_ret_id(rhs->var);
		((function_info *)(cnode->aux))->set_ret_type();
	}
   }
}

gimple_stmt_iterator split_bb_at_stmt (basic_block & bb, gimple stmt, struct cgraph_node *cnode)
{
//	if (!gsi_end_p (gsi_start_bb (bb)))
//		print_gimple_stmt (dump_file, gsi_stmt (gsi_start_bb (bb)), 0, 0);
	edge e = split_block (bb, stmt);
	bb = e->dest;
	if (!gsi_end_p (gsi_start_bb (bb)))
//		print_gimple_stmt (dump_file, gsi_stmt (gsi_start_bb (bb)), 0, 0);
		initialize_block_aux (bb, cnode);
	return gsi_start_bb (bb);
}

void initialize_block_aux (basic_block block, struct cgraph_node *cnode)
{
	// block->aux = (block_information *) ggc_alloc_cleared_atomic (sizeof (block_information));
	block->aux = new block_information(cnode);
}

void delete_block_aux()
{
        struct cgraph_node * cnode;
	basic_block endbb;

        for (cnode = cgraph_nodes; cnode; cnode = cnode->next)
        {
                if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
	                continue;
                push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));


		#if 0
		endbb = EXIT_BLOCK_PTR_FOR_FUNCTION (DECL_STRUCT_FUNCTION (cnode->decl));

		if (endbb->aux)
		{
			delete (block_information *)endbb->aux;
			endbb->aux = NULL;
		}
		#endif

                basic_block bb;
                FOR_EACH_BB (bb) {
                        if (bb->aux)
                        {
//#if GC
//				fprintf (dump_file, "\nGC block");
                                delete (block_information *)bb->aux;
                                bb->aux = NULL;
                        }
                }
                pop_cfun();
        }
}

bool is_function_worklist_empty()
{
	for(int i = 1; i < func_count; i++)
	{
		if(function_worklist[i])
		{
			return false;
		}
	}

	return true;
}

bool is_function_worklist_d_empty()
{
	for(int i = 1; i < func_count_d; i++)
	{
		if(function_worklist_d[i])
		{
			return false;
		}
	}

	return true;
}

void depth_ordering(struct cgraph_node *cnode)
{
	struct cgraph_edge *edge;

	struct cgraph_node *node;

//	fprintf(dump_file,"\nFunction calling depth_ordering %s\n",cgraph_node_name(cnode));

	#if 0
	if(((function_info *)(cnode->aux))->ordered)
	{
		return;

	}
	#endif	

	((function_info *)(cnode->aux))->ordered = true;

	for(edge = cnode->callees; edge; edge = edge->next_callee)
	{
		node = edge->callee;

//		fprintf(dump_file,"\nhiiiiiiii\n");
//		fprintf(dump_file,"\nCallee %s\n",cgraph_node_name(node));

		if (!gimple_has_body_p (node->decl) || node->clone_of)
			continue;
	
		if(!((function_info *)(node->aux))->ordered)
		{
			depth_ordering(node);
		}	
	}

//	fprintf(dump_file,"\nDepth Order %d set for Function %s\n",func_count, cgraph_node_name(cnode));

//	index_func_array[func_count] = cnode;
//	func_index_array[cnode->uid] = func_count;
//	function_worklist[func_count++] = true;

}

void create_depth_ordering()
{
	struct cgraph_node *cnode;

	for (cnode=cgraph_nodes; cnode; cnode=cnode->next) 
	{
       
        	if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
	          continue;
	
//		fprintf(dump_file, "\nFunction %s Order %d\n", cgraph_node_name(cnode), cnode->order);

	        push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

		depth_ordering(cnode);

	}

}

set< unsigned int > nodes_visited_callees;
unsigned int call_depth, call_temp;

void get_trans_callees(struct cgraph_node *cnode)
{
	struct cgraph_node *node;
	struct cgraph_edge *edge;

	nodes_visited_callees.insert(((function_info *)(cnode->aux))->func_num);

	for(edge = cnode->callees; edge; edge = edge->next_callee)
	{
		node = edge->callee;

		if (!gimple_has_body_p (node->decl) || node->clone_of)
			continue;

		((function_info *)(cnode->aux))->trans_callees.insert(((function_info *)(node->aux))->func_num);

		if(find(nodes_visited_callees.begin(), nodes_visited_callees.end(), ((function_info *)(node->aux))->func_num) == nodes_visited_callees.end())
		{
			call_temp++;
			get_trans_callees(node);
		}
//		else
		{
//			call_temp = INFINITY;
		}

		((function_info *)(cnode->aux))->trans_callees.insert(((function_info *)(node->aux))->trans_callees.begin(), ((function_info *)(node->aux))->trans_callees.end());

		if(call_depth < call_temp)
		{
			call_depth = call_temp;
		}

		call_temp = 0;
	}
	
}

void get_callees()
{
	int i = 1;

	struct cgraph_node *cnode;

	for(i; i < func_count; i++)
	{
		call_depth = 0;
		call_temp = 0;

		cnode = func_numbering[index_func_array[i]];
		nodes_visited_callees.clear();

		get_trans_callees(cnode);

		((function_info *)(cnode->aux))->max_depth = call_depth;
	}
}

void initialization (void) 
{ 
   struct cgraph_node * cnode = NULL; 
  // init_alias_heapvars (); 
   cs_init_alias_vars (cnode); 

   for (cnode = cgraph_nodes; cnode; cnode = cnode->next) { 
 
       struct cgraph_node *alias; 
       csvarinfo_t vi; 
 
       /* Nodes without a body, and clone nodes are not interesting. */ 
       if (!gimple_has_body_p (cnode->decl) || cnode->clone_of) 
           continue; 
       /* locating main function. */ 
//     if (strcmp (cgraph_node_name (cnode), "int main()") == 0)
       if (strcmp (IDENTIFIER_POINTER (DECL_NAME (cnode->decl)), "main") == 0)
       {
           main_cnode = cnode; 
	   main_firstbb = start_bb_of_fn (cnode);
       }
 
       // Creates csvarinfo_t for this function and its parameters and local variables 
       vi = cs_create_func_info_for (cnode->decl, cgraph_node_name (cnode), cnode); 
 
        /* CHANGE due gcc-4.7.2 */ 
	 cgraph_for_node_and_aliases (cnode, associate_varinfo_to_alias, vi, true); 

	((function_info *)(cnode->aux))->func_num = func_num;

//	fprintf(dump_file,"\nInitialize %s %d\n", cgraph_node_name(cnode), func_num);

	func_numbering[func_num] = cnode;
	func_num++;

	if(call_indirectly(cnode))
	{
		indirect_cnodes.insert(cnode);
	}	

	get_pred_count(cnode);
 
       /* Associate the varinfo node with all aliases.   
       for (alias = cnode->same_body; alias; alias = alias->next) 
           cs_insert_vi_for_tree (alias->decl, vi);*/ 
   }

	#if 0
 	index_func_array = XNEWVEC (unsigned int, func_num);
 	index_func_array_d = XNEWVEC (unsigned int, func_num);

 	func_index_array = XNEWVEC (unsigned int, func_num);
 	func_index_array_d = XNEWVEC (unsigned int, func_num);

 	function_worklist = XNEWVEC (bool, func_num);
 	function_worklist_d = XNEWVEC (bool, func_num);
 	preprocess_worklist = XNEWVEC (bool, func_num);

	for(int i = 0; i < func_num; i++)
	{
		index_func_array[i] = 0;
		index_func_array_d[i] = 0;

		func_index_array[i] = 0;
		func_index_array_d[i] = 0;

		function_worklist[i] = false;
		function_worklist_d[i] = false;
		preprocess_worklist[i] = false;
	}
	#endif

	func_num--;

	#if STATS
	starttime();
	#endif

//   	find_interval_first_phase(((function_info *)(main_cnode->aux))->func_num);

	#if STATS
	get_callees();
	#endif

	#if STATS
	temptime = stoptime();

//	fprintf(dump_file,"\nInterval Analysis Time %lg\n", temptime);
//	fprintf(dump_file,"\nFunction Ordering Done\n");
	#endif

//	depth_ordering(main_cnode);

	#if 0

	if(main_cnode != NULL)
	{
		fprintf(dump_file,"\nMain Node %s\n", cgraph_node_name(main_cnode));

	  	depth_ordering(main_cnode);	 
	}
	#endif

//	fprintf(dump_file,"\nHelloooooohdkjsdhk\n");

	#if 0
	for(cnode_it; cnode_it != order_func.rend(); cnode_it++)
	{
		cnode = *cnode_it;
		func_worklist.push_back(cnode); //push_front(cnode);
		fprintf(dump_file,"\nFunction in the Worklist %s func_num %d \n",cgraph_node_name(cnode), ((function_info *)(cnode->aux))->func_num);
//		break;
	}
	#endif

	set_cnodes_call_graph.insert(main_cnode);

	f = fopen("call_graph.dot", "w");

	fprintf(f,"digraph callgraph {\n");
	
	get_total_cnodes(main_cnode);

	fprintf(f,"}");

	fclose(f);

//	fprintf(dump_file,"\nTotal Cnodes in Call Graph %d\n", set_cnodes_call_graph.size());

//	fprintf(dump_file,"\nFunctions in All %d\n", test_func_count);

}

gimple_stmt_iterator split_block_at_stmt (gimple statement, basic_block block, struct cgraph_node *cnode)
{
	edge e = split_block (block, statement);
	block = e->dest;

	// Initialize the newly created basic block
	initialize_block_aux (block, cnode);

	return gsi_start_bb (block);
}


void print_variable_data ()
{
	for (int index = 0; index < VEC_length (csvarinfo_t, csvarmap); index++)
	{
	        csvarinfo_t varinfo = VEC_index (csvarinfo_t, csvarmap, index);
		fprintf (dump_file, "\nVar %d - %s", varinfo->id, varinfo->name);
	}
}

void print_assignment_data ()
{
	for (int index = 0; index < VEC_length (constraint_t, aliases); index++)
	{
	        constraint_t assignment = VEC_index (constraint_t, aliases, index);
        	constraint_expr lhs = assignment->lhs;
	        constraint_expr rhs = assignment->rhs;
        	csvarinfo_t lhs_variable = VEC_index (csvarinfo_t, csvarmap, lhs.var);
	        csvarinfo_t rhs_variable = VEC_index (csvarinfo_t, csvarmap, rhs.var);
                fprintf(dump_file,"\nConstraint index: %d LHS Op: %s LHS type: %d LHS ID: %d \n RHS Op: %s RHS type: %d RHS ID: %d \n", 
			index, lhs_variable->name, lhs.type, lhs_variable->id, rhs_variable->name, rhs.type, rhs_variable->id);
	}
}

void print_variable_data (int index)
{
        csvarinfo_t variable = VEC_index (csvarinfo_t, csvarmap, index);

	csvarinfo_t vi;
//	for (vi = variable; vi; vi = vi->next)
}

void print_assignment_data (int index)
{
        constraint_t assignment = VEC_index (constraint_t, aliases, index);
        constraint_expr lhs = assignment->lhs;
        constraint_expr rhs = assignment->rhs;
        csvarinfo_t lhs_variable = VEC_index (csvarinfo_t, csvarmap, lhs.var);
        csvarinfo_t rhs_variable = VEC_index (csvarinfo_t, csvarmap, rhs.var);
	struct cgraph_node * lhs_fn = lhs_variable->scoping_function;
	struct cgraph_node * rhs_fn = rhs_variable->scoping_function;
	const char * lhs_fn_name = NULL, * rhs_fn_name = NULL;
	if (lhs_fn) lhs_fn_name = cgraph_node_name (lhs_fn);
	if (rhs_fn) rhs_fn_name = cgraph_node_name (rhs_fn);
        fprintf(dump_file,"\nConstraint index: %d LHS Op: %s LHS type: %d LHS ID: %d Function %s \n RHS Op: %s RHS type: %d RHS ID: %d Function %s\n", 
		index, lhs_variable->name, lhs.type, lhs_variable->id, lhs_fn_name,
		rhs_variable->name, rhs.type, rhs_variable->id, rhs_fn_name);
}

void print_parsed_data (basic_block current_block)
{


}

void print_parsed_data ()
{

   	struct cgraph_node * cnode = NULL; 
	for (cnode = cgraph_nodes; cnode; cnode = cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		basic_block current_block;
		FOR_EACH_BB (current_block) 
		{
//			print_parsed_data (current_block);
		}

		pop_cfun();
	}
}


void init_fn_aux()
{
	struct cgraph_node *cnode;
	for (cnode=cgraph_nodes; cnode; cnode=cnode->next) {
		basic_block current_block;
        if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
          continue;
        push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));
        cnode->aux = new function_info();
        pop_cfun();
	}
}

void end_fn_aux()
{
	struct cgraph_node *cnode;
	int *x;
	bool *y;
for (cnode=cgraph_nodes; cnode; cnode=cnode->next) {

if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
        continue;
        push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));


        if(cnode->aux)
                {
		#if 0
		free (((function_info *)(cnode->aux))->rev_post_order);
//		free (x);
//		((function_info *)(cnode->aux))->set_rev_post_order(x);

		free (((function_info *)(cnode->aux))->get_bb_order());
//		delete (x);
//		((function_info *)(cnode->aux))->set_bb_order(x);

		y = ((function_info *)(cnode->aux))->get_live_worklist();
		delete (y);
		((function_info *)(cnode->aux))->set_live_worklist(y);

		y = ((function_info *)(cnode->aux))->get_points_worklist();
		delete (y);
		((function_info *)(cnode->aux))->set_points_worklist(y);

		#endif
                delete (function_info *)cnode->aux;
                cnode->aux = NULL;
                }

        pop_cfun();
        }
}


void print_original_cfg ()
{
//	FUNCTION_NAME ();

   	struct cgraph_node * cnode = NULL; 
	for (cnode = cgraph_nodes; cnode; cnode = cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		int n = 1;
		basic_block current_block;
		FOR_EACH_BB (current_block) 
		{
			gimple_stmt_iterator gsi;
			for (gsi = gsi_start_bb (current_block); !gsi_end_p (gsi); gsi_next (&gsi))
			{
				print_gimple_stmt (dump_file, gsi_stmt (gsi), 0, 0);
			}
		}

		pop_cfun();
	}
}

/* ----------------------------------------------------------------
   Restoring the cfg by clearing the aux field of each basic block
   and removing unnecessary (split) blocks.
   ---------------------------------------------------------------*/
void restore_control_flow_graph ()
{
//	FUNCTION_NAME ();

   struct cgraph_node * cnode;
   for (cnode = cgraph_nodes; cnode; cnode = cnode->next) 
   {
       if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
           continue;

       push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));
       // current_function_decl = cnode->decl;
       // set_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

       /* Free cgraph node's aux field. */
       if (cnode->aux) {
           ggc_free (cnode->aux);
           cnode->aux = NULL;
       }
       /* Free each bb's aux field. */
       basic_block cbb;
       FOR_EACH_BB (cbb) {
           if (cbb->aux) {
               ggc_free (cbb->aux);
               cbb->aux = NULL;
           }
       }
       /* Merge bb's if necessary. */
       cleanup_tree_cfg ();
       /* Free the dominator info. */
       free_dominance_info (CDI_DOMINATORS);
       free_dominance_info (CDI_POST_DOMINATORS);
   
       pop_cfun ();
   }
}

bool check_if_var_temp(unsigned int var)
{
	if(var <= 3)
	{
		return false;
	}

	tree decl = VEC_index(csvarinfo_t, csvarmap, var)->decl;

	if(!decl)
	{
		return false;
	}

	if(DECL_ARTIFICIAL(decl))
	{
		return true;
	}
	else
	{
		return false;
	}
}

#if 1
void boundary_info(struct cgraph_node *cnode)
{
	basic_block bb;
	it ai;

	live_type temp_live;
	live_info live_vars;

//	fprintf(dump_file,"\nInside boundary_info\n");

//	fprintf(dump_file,"\nInside boundary_info Function %s\n", cgraph_node_name(cnode));

//	if(cgraph_node_name(cnode) == "main")
	if (strcmp (IDENTIFIER_POINTER (DECL_NAME (cnode->decl)), "main") == 0)
	{
//		fprintf(dump_file,"\nMain Function Don't Do anything\n");
		return;
	}

	il il1, il2;

	il1.add_deref(-1); // il for x->x' edge

	for(int i = 0; i < infi_thresh; i++)
	{
		il2.add_deref(-1);
	}	
	il2.set_infinity(); // il for x'->x' edge

	Node lhs, rhs;

	set_edges edges_add;

//	fprintf(dump_file,"\nInside Boundary Info\n");

	FOR_EACH_BB (bb)
        {
		if(bb_call_stmt(bb) != NULL)
		{
			// Its a call block

			((function_info *)(cnode->aux))->call_block_list.insert(bb->index);
		}
			
		constraint_list con = ((block_information *)(bb->aux))->get_list();
		
		for(ai = con.begin(); ai != con.end(); ai++ )
	        {
        	        if(!(*ai).get_bool())
                	        continue;

			constraint_t c = VEC_index(constraint_t, aliases, (*ai).get_int());

			if(c->lhs.var < 3)
				continue;

			if(c->rhs.var == 1 || c->rhs.var == 2 || c->rhs.var == 3)	
				continue;

			if(!check_if_var_temp(c->lhs.var))
			{

				// Creating x->x' edges

				lhs.set_var_id(c->lhs.var);
				lhs.set_ind_list(il1);

				lhs.add_node_map();
	
				rhs.set_var_id((c->lhs.var)+1);
				rhs.set_ind_list(il1);
	
				rhs.add_node_map();

				Edge e_lhs(lhs,rhs);

//				fprintf(dump_file,"\nLHS x->x' Edge\n");
//				print_edge_id(e_lhs.get_edge_id());

				edges_add.insert(e_lhs.get_edge_id());

				// Creating x'->x' edges

				lhs.set_var_id((c->lhs.var)+1);
				lhs.set_ind_list(il1);

				lhs.add_node_map();

				rhs.set_var_id((c->lhs.var)+1);
				rhs.set_ind_list(il2);

				rhs.add_node_map();

				Edge e_lhs_loop(lhs,rhs);

//				fprintf(dump_file,"\nLHS x'->x' Edge\n");
//				print_edge_id(e_lhs_loop.get_edge_id());

				edges_add.insert(e_lhs_loop.get_edge_id());
			}

			if(!check_if_var_temp(c->rhs.var))
			{	
			
				if(c->rhs.type != 0)
				{

					lhs.set_var_id(c->rhs.var);
					lhs.set_ind_list(il1);

					lhs.add_node_map();
	
					rhs.set_var_id((c->rhs.var)+1);
					rhs.set_ind_list(il1);

					rhs.add_node_map();

					Edge e_rhs(lhs,rhs);

//					fprintf(dump_file,"\nRHS x->x' Edge\n");
//					print_edge_id(e_rhs.get_edge_id());

					edges_add.insert(e_rhs.get_edge_id());

					lhs.set_var_id((c->rhs.var)+1);
					lhs.set_ind_list(il1);

					lhs.add_node_map();
	
					rhs.set_var_id((c->rhs.var)+1);
					rhs.set_ind_list(il2);

					rhs.add_node_map();

					Edge e_rhs_loop(lhs,rhs);

//					fprintf(dump_file,"\nRHS x'->x' Edge\n");
//					print_edge_id(e_rhs_loop.get_edge_id());

					edges_add.insert(e_rhs_loop.get_edge_id());

				}
			}

		}
	}

	set<unsigned int> paras = ((function_info *)(cnode->aux))->get_params();

	if(((function_info *)(cnode->aux))->has_ret_type())
	{
		unsigned int ret_id = ((function_info *)(cnode->aux))->get_ret_id();
		temp_live.insert(ret_id);
	}

	set<unsigned int>::iterator pit = paras.begin();

	for(pit; pit != paras.end(); pit++)
	{
		unsigned int var;

		var = *pit;

		temp_live.insert(var);

		lhs.set_var_id(var);
		lhs.set_ind_list(il1);

		lhs.add_node_map();

		rhs.set_var_id(var+1);
		rhs.set_ind_list(il1);

		rhs.add_node_map();

		Edge e_par(lhs,rhs);

//		fprintf(dump_file,"\nPara x->x' Edge\n");
//		print_edge_id(e_par.get_edge_id());

		edges_add.insert(e_par.get_edge_id());

		lhs.set_var_id(var+1);
		lhs.set_ind_list(il1);

		lhs.add_node_map();

		rhs.set_var_id(var+1);
		rhs.set_ind_list(il2);

		rhs.add_node_map();

		Edge e_par_loop(lhs,rhs);

//		fprintf(dump_file,"\nPara x'->x' Edge\n");
//		print_edge_id(e_par_loop.get_edge_id());

		edges_add.insert(e_par_loop.get_edge_id());

	}

	live_vars.set_l_info(temp_live);
	live_vars.reset_deref();

	DVG g;

	bb = start_bb_of_fn(cnode);
	g.add_edges(bb, edges_add, cnode, 0, false);

//	fprintf(dump_file,"\nStart Block in boundary %d\n",bb->index);
		
	((block_information *)(bb->aux))->set_points_in(g);

	bb = end_bb_of_fn(cnode);
//	fprintf(dump_file,"\nEnd Block in boundary %d\n",bb->index);
	((block_information *)(bb->aux))->set_live_out(live_vars);

	#if TRACE
//	fprintf(dump_file,"\nFunction %s Basic Block %d Initialized\n",cgraph_node_name(cnode),bb->index);
//	g.print_dvg();
	#endif

	#if 0
	set_edges eset = ((block_information *)(bb->aux))->get_points_in().get_edge_list();

	edge_id_it edt = eset.begin();
	for(edt; edt != eset.end(); edt++)
	{
		Edge et = get_edge_map(*edt);
//		et.print_edge();
	}
	#endif	
}
#endif

void set_boundary_live()
{
	live_type temp_live;
	basic_block bb;
	unsigned int var;
	live_info live_vars;
	
	struct cgraph_node *cnode;

	for (cnode=cgraph_nodes; cnode; cnode=cnode->next)
	{
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
        		continue;

		push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

		set<unsigned int> paras = ((function_info *)(cnode->aux))->get_params();

		if(((function_info *)(cnode->aux))->has_ret_type())
		{
			unsigned int ret_id = ((function_info *)(cnode->aux))->get_ret_id();
			temp_live.insert(ret_id);
		}

		set<unsigned int>::iterator pit = paras.begin();

		for(pit; pit != paras.end(); pit++)
		{
			var = *pit;

			temp_live.insert(var);
		}

		live_vars.set_l_info(temp_live);
		live_vars.reset_deref();

		bb = end_bb_of_fn(cnode);
		((block_information *)(bb->aux))->set_live_out(live_vars);

		pop_cfun();
	}
}

void set_boundary_points()
{
	basic_block bb;
	DVG g;
	it ai;
	Node lhs, rhs;
	set_edges edges_add;
	unsigned int var;

	struct cgraph_node *cnode;

	for (cnode=cgraph_nodes; cnode; cnode=cnode->next)
	{
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
        		continue;

		push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

		if (strcmp (IDENTIFIER_POINTER (DECL_NAME (cnode->decl)), "main") == 0)
		{
			return;
		}

		il il1, il2;

		il1.add_deref(-1); // il for x->x' edge

		for(int i = 0; i < infi_thresh; i++)
		{
			il2.add_deref(-1);
		}	
		il2.set_infinity(); // il for x'->x' edge

		FOR_EACH_BB (bb)
        	{
			constraint_list con = ((block_information *)(bb->aux))->get_list();
		
			for(ai = con.begin(); ai != con.end(); ai++ )
		        {
        		        if(!(*ai).get_bool())
                		        continue;

				constraint_t c = VEC_index(constraint_t, aliases, (*ai).get_int());

				if(c->lhs.var < 3)
					continue;

				if(c->rhs.var == 1 || c->rhs.var == 2 || c->rhs.var == 3)	
					continue;

				if(!check_if_var_temp(c->lhs.var))
				{

					// Creating x->x' edges

					lhs.set_var_id(c->lhs.var);
					lhs.set_ind_list(il1);

					lhs.add_node_map();
	
					rhs.set_var_id((c->lhs.var)+1);
					rhs.set_ind_list(il1);
	
					rhs.add_node_map();

					Edge e_lhs(lhs,rhs);

					edges_add.insert(e_lhs.get_edge_id());

					// Creating x'->x' edges
	
					lhs.set_var_id((c->lhs.var)+1);
					lhs.set_ind_list(il1);

					lhs.add_node_map();

					rhs.set_var_id((c->lhs.var)+1);
					rhs.set_ind_list(il2);

					rhs.add_node_map();

					Edge e_lhs_loop(lhs,rhs);

					edges_add.insert(e_lhs_loop.get_edge_id());
				}

				if(!check_if_var_temp(c->rhs.var))
				{	
			
					if(c->rhs.type != 0)
					{

						lhs.set_var_id(c->rhs.var);
						lhs.set_ind_list(il1);
	
						lhs.add_node_map();
	
						rhs.set_var_id((c->rhs.var)+1);
						rhs.set_ind_list(il1);

						rhs.add_node_map();

						Edge e_rhs(lhs,rhs);
	
						edges_add.insert(e_rhs.get_edge_id());

						lhs.set_var_id((c->rhs.var)+1);
						lhs.set_ind_list(il1);

						lhs.add_node_map();
	
						rhs.set_var_id((c->rhs.var)+1);
						rhs.set_ind_list(il2);

						rhs.add_node_map();

						Edge e_rhs_loop(lhs,rhs);
	
						edges_add.insert(e_rhs_loop.get_edge_id());

					}
				}

			}
		}

		set<unsigned int> paras = ((function_info *)(cnode->aux))->get_params();

		set<unsigned int>::iterator pit = paras.begin();

		for(pit; pit != paras.end(); pit++)
		{
			var = *pit;

			lhs.set_var_id(var);
			lhs.set_ind_list(il1);

			lhs.add_node_map();

			rhs.set_var_id(var+1);
			rhs.set_ind_list(il1);

			rhs.add_node_map();

			Edge e_par(lhs,rhs);

			edges_add.insert(e_par.get_edge_id());

			lhs.set_var_id(var+1);
			lhs.set_ind_list(il1);

			lhs.add_node_map();

			rhs.set_var_id(var+1);
			rhs.set_ind_list(il2);

			rhs.add_node_map();

			Edge e_par_loop(lhs,rhs);

			edges_add.insert(e_par_loop.get_edge_id());

		}

		bb = start_bb_of_fn(cnode);
		g.add_edges(bb, edges_add, cnode, 0, false);

//		bb = start_bb_of_fn(cnode);
		((block_information *)(bb->aux))->set_points_in(g);

		pop_cfun();
	}

}

void initialize_worklist(struct cgraph_node *cnode, basic_block endblock, int *rp, int *pp, int num_bb)
{
	int i;
	basic_block bt;
	
//	memcpy(((function_info *)(cnode->aux))->rev_post_order, rp, num_bb * sizeof(int));
//	memcpy(((function_info *)(cnode->aux))->post_order, pp, num_bb * sizeof(int));

//	fprintf(dump_file,"\nNumber of Blocks %d\n", num_bb+1);
//	fprintf(dump_file,"\nEnd Block Index %d\n",endblock->index);
	#if 1
//	fprintf(dump_file,"\nFunction %s\n",cgraph_node_name(cnode));

//	fprintf(dump_file,"\nReverse Post Order\n");

	for(i = 0; i < num_bb; i++)
	{
		((function_info *)(cnode->aux))->rev_post_order[i] = rp[i];

		bt = BASIC_BLOCK(((function_info *)(cnode->aux))->rev_post_order[i]);

//		fprintf(dump_file,"\nbt->index %d\n",bt->index);

		((function_info *)(cnode->aux))->bb_rp_order[bt->index] = i;

//		((function_info *)(cnode->aux))->live_worklist[i] = false;
		((function_info *)(cnode->aux))->points_worklist[i] = false;
	}

//	((function_info *)(cnode->aux))->bb_rp_order[1] = i;
//	((function_info *)(cnode->aux))->points_worklist[i] = false;
	#endif

	#if 1
//	fprintf(dump_file,"\nPost Order\n");

	for(i = 0; i < num_bb; i++)
	{
		((function_info *)(cnode->aux))->post_order[i] = pp[i];

		bt = BASIC_BLOCK(((function_info *)(cnode->aux))->post_order[i]);

//		fprintf(dump_file,"\nbt->index %d\n",bt->index);

		((function_info *)(cnode->aux))->bb_p_order[bt->index] = i;

		((function_info *)(cnode->aux))->live_worklist[i] = true;
//		((function_info *)(cnode->aux))->points_worklist[i] = false;
	}	

//	fprintf(dump_file,"\nOrdering Done\n");

//	((function_info *)(cnode->aux))->bb_p_order[2] = i;
//	((function_info *)(cnode->aux))->live_worklist[i] = false;

	((function_info *)(cnode->aux))->live_worklist[0] = true;
	((function_info *)(cnode->aux))->points_worklist[0] = true;
	#endif
//	fprintf(dump_file,"\nHiiiii\n");

	#if 0
	int *bb;

	bool *l_wk, *p_wk;

	int i;
	basic_block bt;

	((function_info *)(cnode->aux))->rev_post_order = XNEWVEC (int, num_bb);
	((function_info *)(cnode->aux))->bb_order = XNEWVEC (int, num_bb+2);
	((function_info *)(cnode->aux))->live_worklist = XNEWVEC (bool, num_bb+2);
	((function_info *)(cnode->aux))->points_worklist = XNEWVEC (bool, num_bb+2);

	memcpy(((function_info *)(cnode->aux))->rev_post_order, rp, num_bb * sizeof(int));

	bb = XNEWVEC (int, num_bb+2);

	l_wk = XNEWVEC (bool, num_bb+2);
	p_wk = XNEWVEC (bool, num_bb+2);

	fprintf(dump_file,"\nNumber of Blocks %d\n", num_bb+1);
	fprintf(dump_file,"\nEnd Block Index %d\n",endblock->index);

	for(i = 0; i < num_bb; i++)
	{
		bt = BASIC_BLOCK(((function_info *)(cnode->aux))->rev_post_order[i]);

		fprintf(dump_file,"\nbt->index %d\n",bt->index);

		bb[bt->index] = i;

		l_wk[i] = false;

		l_wk[i] = false;
	}

//	bb[endblock->index] = i;

	l_wk[i-1] = true;

	p_wk[0] = true;

	int x = num_bb + 2;
	memcpy(((function_info *)(cnode->aux))->bb_order, bb, x * sizeof(int));
	memcpy(((function_info *)(cnode->aux))->live_worklist, l_wk, x * sizeof(bool));
	memcpy(((function_info *)(cnode->aux))->points_worklist, p_wk, x * sizeof(bool));

	free (bb);
	free (l_wk);
	free (p_wk);
	#endif
}

void get_pred_count(struct cgraph_node *cnode)
{
	struct cgraph_edge *edge;
	unsigned int x = 0;

	for(edge = cnode->callers; edge; edge = edge->next_caller)
	{
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		++x;
	}

	((function_info *)(cnode->aux))->set_pred_count(x);
}

void get_total_cnodes(struct cgraph_node *cnode)
{
	//ADDED: anubhav
	if(!cnode)
		return;

	struct cgraph_edge *edge;
	struct cgraph_node *node;

//	if (strcmp (IDENTIFIER_POINTER (DECL_NAME (cnode->decl)), "encode_one_frame") == 0)
//		print = true;	

	for(edge = cnode->callees; edge; edge = edge->next_callee)
	{
		node = edge->callee;

		if (!gimple_has_body_p (node->decl) || node->clone_of)
			continue;

//		if(print)
		fprintf(f, "\"%s\" -> \"%s\";\n", cgraph_node_name(cnode), cgraph_node_name(node));

//		((function_info *)(cnode->aux))->callee_count++; // = ((function_info *)(node->aux))->callee_count;

		if(set_cnodes_call_graph.find(node) == set_cnodes_call_graph.end())
		{
			set_cnodes_call_graph.insert(node);

			get_total_cnodes(node);
		}


//		((function_info *)(cnode->aux))->callee_count += ((function_info *)(node->aux))->callee_count;
	}

}

bool call_indirectly(struct cgraph_node *cnode) // Returns true if this function is called indirectly
{
	struct cgraph_edge *edge;

	struct cgraph_node *node;

	int x = 0, y = 0;

	for(edge= cnode->callers; edge; edge = edge->next_caller)
	{
		node = edge->caller;

		if (!gimple_has_body_p (node->decl) || node->clone_of)
			continue;

		x++;
	}

	for(edge= cnode->callees; edge; edge = edge->next_callee)
	{
		node = edge->callee;

		if (!gimple_has_body_p (node->decl) || node->clone_of)
			continue;

		y++;
	}

	if(x > 0 || y > 0)
	{
		return false;
	}
	else
	{
		return true;
	}
	
}

void construct_summary_flow_function_of_bb()
{
	struct cgraph_node *cnode;
	basic_block bb;

//	fprintf(dump_file,"\nConstruct Summary Flow Function of Basic Block\n");

	for (cnode=cgraph_nodes; cnode; cnode=cnode->next)
	{
       
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
        		  continue;

		push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

		FOR_EACH_BB(bb)
		{	
			DVG new_dvg;

			it ai;
			for(ai= ((block_information *)(bb->aux))->get_list().begin();ai !=((block_information *)(bb->aux))->get_list().end(); ai++ )
			{
				if(!(*ai).get_bool())
				{
					continue;
				}

				constraint_t con = VEC_index(constraint_t, aliases, (*ai).get_int());
				new_dvg.generate_graph(bb, con, cnode, (*ai).get_int());
			}
			
//			fprintf(dump_file,"\nFunction %s Basic Block Index %d DVG\n", cgraph_node_name(cnode), bb->index);
//			new_dvg.print_dvg();

			((block_information *)(bb->aux))->set_summ(new_dvg);
		}
		pop_cfun();
	}
}

void process_call_pt(struct cgraph_node *cnode, basic_block bb, gimple stmt)
{
	struct cgraph_node *node;
	callpt_type temp;

	tree decl = get_called_fn_decl (stmt);

	if (TREE_CODE (decl) == FUNCTION_DECL)
	{
		node = cgraph_get_node(decl);

		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
                          return;

		temp = make_tuple(((function_info *)(cnode->aux))->func_num, bb->index);
		((function_info *)(node->aux))->call_pts.insert(temp);
	}
	else
	{
		return;
	}	
}

void preprocess_cnode(struct cgraph_node *cnode)
{
	basic_block current_block;

	basic_block endblock = NULL;

	bool is_start_block = true;

	FOR_EACH_BB (current_block) 
	{
		num_bb_count++;
		 if(current_block->index == 2)
                {
//     	                fprintf(dump_file, "\nFunction Basic Block Push %s\n", cgraph_node_name(cnode));
//            	        ((function_info *)(cnode->aux))->push_front(current_block,2);
               	}

		gimple_stmt_iterator gsi;
		bool has_phi = false;

		// Initialize auxillary info.
		if (!current_block->aux)
		{
			initialize_block_aux (current_block,cnode);
		}

		// Identification of start block, Sp 
		if (is_start_block) 
		{
			((block_information *)(current_block->aux))->start_block = true;
			is_start_block = false;
		}

		// Iterate over the statements of current_block.
		for (gsi = gsi_start_bb (current_block); !gsi_end_p (gsi); gsi_next (&gsi)) 
		{
			gimple stmt = gsi_stmt (gsi);
//			print_gimple_stmt (dump_file, stmt, 0, 0);

			if (is_gimple_call (stmt) || is_gimple_endblock (stmt)) 
			{
				gimple_stmt_iterator origgsi = gsi;
				tree decl = NULL;

				// Need not break in case of library routines.
				if (is_gimple_call (stmt)) 
				{
					decl = get_called_fn_decl (stmt);
					if (TREE_CODE (decl) == FUNCTION_DECL) 
					{
						if (!DECL_STRUCT_FUNCTION (decl)) 
						{
							process_library_call (stmt, current_block, cnode);
							// A library call is not marked as a call_block
							continue;
						}
					}
				}

				origgsi = gsi;
                                gsi_prev (&gsi);
                                if (!gsi_end_p (gsi))
                                {
 	                                edge e = split_block (current_block,gsi_stmt (gsi));
                                        current_block = e->dest;
                                        if(!current_block->aux)
                                        //        current_block->aux = new block_information(cnode);
						initialize_block_aux (current_block,cnode);	
                                        gsi=gsi_start_bb(current_block);
                                 }
                                 else
                                        gsi = origgsi;

                                 origgsi=gsi;
                                 gsi_next(&gsi);
                                 if(!gsi_end_p(gsi))
                                 {
                	                  gsi=origgsi;
                                          split_block (current_block,gsi_stmt (gsi));
                                          if(!current_block->aux)
//                      	                  current_block->aux = new block_information(cnode);
						  initialize_block_aux (current_block,cnode);
                                 }
                                 else
                                          gsi=origgsi;

				if (is_gimple_call (stmt)) 
				{
					call_site_count++;
					((function_info *)(cnode->aux))->call_num++;

					bool fptr_call = (TREE_CODE (decl) != FUNCTION_DECL);

					process_call_pt(cnode, current_block, stmt);

					// Mark the calling function pointer as live.
					if (fptr_call) 
					{
	 					unsigned int var = cs_get_vi_for_tree (decl, current_block, cnode)->id;
						generate_liveness_constraint(current_block, var);
					}

					// Mark call current_block with its properties.
					((block_information *)(current_block->aux))->call_block = true; 
						  
					// Discover the static call argument mapping.
					map_arguments_at_call (stmt, decl, fptr_call, current_block, cnode); 

				}

				if (is_gimple_endblock (stmt)) 
				{
					generate_retval_liveness (stmt, current_block, cnode);
					((block_information *)(current_block->aux))->end_block = true;
					((function_info *)(cnode->aux))->end_block_id = current_block->index;
					((function_info *)(cnode->aux))->set_end_block_index(current_block->index);
					endblock = current_block;
				}
			}

			// Inspect other statements for possible pointers.
			else if (is_gimple_assign (stmt)) 
			{
				check_deref = true; 
				process_gimple_assign_stmt (stmt, current_block, cnode);
				check_deref = false;
			}

			else if (gimple_code (stmt) == GIMPLE_COND) 
			{
				process_gimple_condition (stmt, current_block, cnode); 
			}

		}

	}

	#if 0
	if (!endblock) 
	{
		endblock = EXIT_BLOCK_PTR_FOR_FUNCTION (DECL_STRUCT_FUNCTION (cnode->decl))->prev_bb;
		((function_info *)(cnode->aux))->set_num_bb(total_bbs);
	}
	#endif
	
	((function_info *)(cnode->aux))->set_num_bb(total_bbs);
//	unsigned int size = ((function_info *)(cnode->aux))->get_num_bb();

//	fprintf(dump_file,"\nFunction %s has Total Basic Blocks %d\n",cgraph_node_name(cnode), ((function_info *)(cnode->aux))->get_num_bb());
//	fprintf(dump_file,"\nToooo Muchhhhhhhh13`33444\n");

	int *rp, *pp;
	rp = XNEWVEC (int, total_bbs);
	pre_and_rev_post_order_compute (NULL, rp, false);
	pp = XNEWVEC (int, total_bbs);
//	fprintf(dump_file,"\nToooo Muchhhhhhhhhdihfihrfjlkf\n");
	post_order_compute (pp, false, true);
//	fprintf(dump_file,"\nToooo Muchhhhhhhh\n");

	initialize_worklist(cnode, endblock, rp, pp, total_bbs);
	
	free (rp);
	free (pp);
		
//	fprintf(dump_file,"\nHelloooooo\n");

	// Vini, June'15: Commented out
//	boundary_info(cnode);
}

void preprocess_control_flow_graph()
{
	bool is_start_block;
	struct cgraph_node * cnode;
	basic_block endbb;

//	for(int i = 0; i <= func_num; i++)
	for (cnode=cgraph_nodes; cnode; cnode=cnode->next) 
	{
//		cnode = func_numbering[i];

//		fprintf(dump_file,"\nI %d Index %d\n", i, index_func_array_d[i]);

//		cnode = func_numbering[index_func_array_d[i]];

		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		test_func_count++;

//		fprintf(dump_file,"\nPreprocess %s\n", cgraph_node_name(cnode));
 
//		order_func.push_back(cnode);

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));


		#if 0
		endbb = EXIT_BLOCK_PTR_FOR_FUNCTION (DECL_STRUCT_FUNCTION (cnode->decl));
		fprintf(dump_file,"\nUnique %d\n",endbb->index);

		if (!endbb->aux)
		{
			initialize_block_aux (endbb,cnode);
		}
		#endif

		preprocess_cnode(cnode);

		pop_cfun();
	}


	#if 0
	set< struct cgraph_node * >::iterator ic;

	for(ic = indirect_cnodes.begin(); ic != indirect_cnodes.end(); ic++)
	{
		cnode = *ic;

		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

//		fprintf(dump_file,"\nPreprocess %s\n", cgraph_node_name(cnode));
 
		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		preprocess_cnode(cnode);

		pop_cfun();
		
	}
	#endif

//	func_num--;

	globals.erase(0);
	globals.erase(1);
	globals.erase(2);
	globals.erase(3);
	set<unsigned int>::iterator g_it;
	for(g_it=globals.begin();g_it != globals.end(); g_it++)
	{
		csvarinfo_t v = VEC_index(csvarinfo_t,csvarmap,*g_it);

		struct cgraph_node *nn = v->scoping_function;

		if(nn->decl == v->decl)
			globals.erase(*g_it);

		if(v->is_art_var)
			globals.erase(*g_it);
//		else if(v->is_heap_var)
//			globals.erase(*g_it);
		
	}

	create_con_dep_node(undef_id);

	order_func.sort();

	cnode_it = order_func.rbegin();
//	struct cgraph_node *cnode;
	
//	fprintf(dump_file,"\nHiiiiiiiiii\n");

//	fprintf(dump_file,"\nBasic Block Summary Construction\n");

	create_undef_node();

	#if DFVSFFCALLBB
	construct_summary_flow_function_of_bb();
	#endif
}

bool is_cdv(unsigned int id)
{
	if(CDV.find(id) != CDV.end())
		return true;
	else
		return false;
}

unsigned int context_dep(unsigned int id) // Given x, return x'
{
	if(CDV.find(id) != CDV.end())
		return id;
	else
		return (id+1);
}

unsigned int context_dep_rev(unsigned int id) // Given x', return x
{
	if(CDV.find(id) != CDV.end())
		return (id-1);
	else
		return id;
}

const char * copy_string(const char * var)
{
        char *temp = (char *)xmalloc(strlen(var)+1);
        strcpy(temp,var);
        const char * temp1 = (const char *)temp;

        return temp1;
}

const char * get_var_name(unsigned int vid)
{
	const char *nn = "i";
        const char *name,*fname;

	fname = copy_string(VEC_index(csvarinfo_t, csvarmap, vid)->name);

	if(CDV.find(vid) != CDV.end())
	{
        	name = copy_string(VEC_index(csvarinfo_t, csvarmap, vid)->name);
                string str = string(name) + string(nn);
                fname = copy_string(str.c_str());
	}

	return fname;
}

//#endif
