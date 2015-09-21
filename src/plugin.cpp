/*-----------------------------------------------------------------------------
 *  "gcc-plugin.h" must be the FIRST file to be included 
 *-----------------------------------------------------------------------------*/
#include "gcc-plugin.h"

#include "tree.h"
#include "basic-block.h"
#include "tree-ssa-alias.h"
#include "gimple.h"
#include "cgraph.h"
#include "tree-pass.h"
#include "gimple-pretty-print.h"

#include <iostream>
using namespace std;

/* global declarations */
static unsigned int execute_gimple_manipulation (void);
static bool gate_gimple_manipulation (void);
void analyze_gimple_statement (void);
void print_call_graph ();

/*-----------------------------------------------------------------------------
 *  Each plugin MUST define this global int to assert compatibility with GPL; 
 *  else the compiler throws a fatal error 
 *-----------------------------------------------------------------------------*/
int plugin_is_GPL_compatible;  

/*-----------------------------------------------------------------------------
 *  Structure of the pass we want to insert, identical to a regular ipa pass
 *-----------------------------------------------------------------------------*/
struct simple_ipa_opt_pass myPass ={
	{
		SIMPLE_IPA_PASS,				//  opt type name
		"demo",							//  name
		 0,                             //  gate 
	     execute_gimple_manipulation,   //  execute function 
		 NULL,                         /*  sub */
		 NULL,                         /*  next */
		 0,                            /*  static pass number */
		 TV_INTEGRATION,               /*  tv_id */
		 0,                           /*  properties required */
		 0,                            /*  properties provided */
		 0,                            /*  properties destroyed */
		 0,                            /*  todo_flags start */
		 0                             /*  todo_flags end */
	}
};


/*-----------------------------------------------------------------------------
 *    This structure provides the information about inserting the pass in the
 *    pass manager. 
 *-----------------------------------------------------------------------------*/
struct register_pass_info pass_info = {
	  &(myPass.pass),            /* Address of new pass, here, the 'struct opt_pass' field of 'simple_ipa_opt_pass'
										 defined above */
	    "pta",                        /* Name of the reference pass for hooking up the new pass.  */

		  0,                          /* Insert the pass at the specified instance number of the reference pass. 
										 Do it for every instance if it is 0. */

		PASS_POS_INSERT_AFTER         /* how to insert the new pass: before, after, or replace. Here we are inserting
								         a pass names 'plug' after the pass named 'pta' */
};


/*-----------------------------------------------------------------------------
 *  plugin_init is the first function to be called after the plugin is loaded
 *-----------------------------------------------------------------------------*/
extern int plugin_init(struct plugin_name_args* plugin_info, struct plugin_gcc_version* version)
{
	  /*-----------------------------------------------------------------------------
	   *     Plugins are activiated using this callback 
	   *-----------------------------------------------------------------------------*/
	   register_callback (
		   plugin_info->base_name,     /* char *name: Plugin name, could be any
		                                  name. plugin_info->base_name gives this filename */
	       PLUGIN_PASS_MANAGER_SETUP,  /* int event: The event code. Here, setting up a new pass */
		   NULL,                       /* The function that handles event */
		   &pass_info);                /* plugin specific data */

	  
	   return 0;

}

/* ---------------------------------------------
   The main driver function to perform analysis.
   ---------------------------------------------*/
static unsigned int execute_gimple_manipulation (void)
{
	if (!dump_file)
		return 1;

	print_call_graph ();

	analyze_gimple_statement ();

	return 0;
}

void print_call_graph ()
{
	/* Structure details in file cgraph.h */
	struct cgraph_node *node;
	struct cgraph_edge *edgei,*e;

	fprintf (dump_file, "\n----- Printing Call Graph -----");
	cout<<"Printing Call Graph."<<endl;
	/* Iterate over all the functions */
	for(node=cgraph_nodes;node;node=node->next)
        {
			/* Nodes without a body, and clone nodes are not interesting. */
			if (!gimple_has_body_p (node->decl) || node->clone_of)
				continue;

			push_cfun (DECL_STRUCT_FUNCTION (node->decl));
			fprintf (dump_file, "\n Function : %s", cgraph_node_name(node));
            /* iterate over the callees */
			for (e = node->callees; e; e = e->next_callee)
				fprintf (dump_file, "\n\t Callee : %s", cgraph_node_name(e->callee));

			pop_cfun ();
        }
}

/* Function to extract and print operands of the assignment statement */
void print_assign_stmt_operands (gimple stmt)
{
	tree lhs_arg = NULL, arg1 = NULL, arg2 = NULL, arg3 = NULL;

	/* Extract operands of the assignment statement 
	   API's can be found in file gimple.h */
	switch (gimple_num_ops (stmt))
        {
        	case 4:
        		arg3 = gimple_assign_rhs3 (stmt);
        	case 3:
          		arg2 = gimple_assign_rhs2 (stmt);
        	case 2:
          		arg1 = gimple_assign_rhs1 (stmt);
			lhs_arg = gimple_assign_lhs (stmt);
          		break;
        	default:
          		gcc_unreachable ();
        }

	/* Print the operands of the assignement statement */
	if (lhs_arg)
	{
		fprintf (dump_file, "\n\t\t\tLhs arg : ");
		print_generic_expr (dump_file, lhs_arg, 0);
	}
	if (arg1)
	{
		fprintf (dump_file, "\n\t\t\tRhs arg1 : ");
		print_generic_expr (dump_file, arg1, 0);
	}
	if (arg2)
	{
		fprintf (dump_file, "\n\t\t\tRhs arg2 : ");
		print_generic_expr (dump_file, arg2, 0);
	}
	if (arg3)
	{
		fprintf (dump_file, "\n\t\t\tRhs arg3 : ");
		print_generic_expr (dump_file, arg3, 0);
	}
}

/* Function to print the operator of the assignment statement*/
void print_assign_stmt_operator (gimple stmt)
{
	switch (gimple_assign_rhs_code (stmt))
	{
		case MULT_EXPR:
			fprintf (dump_file, "\n\t\t\tOperator : Mult");
			break;
		case PLUS_EXPR:
			fprintf (dump_file, "\n\t\t\tOperator : Plus");
			break;
		case MINUS_EXPR:
			fprintf (dump_file, "\n\t\t\tOperator : Minus");
			break;
    		default:
      			fprintf (dump_file, "\n\t\t\tCheck the operator in this statement");
			break;
	}
}

void analyze_gimple_statement ()
{
	fprintf (dump_file, "\n\n----- Classifying Gimple statements -----");
	struct cgraph_node *node;
	//FOR_EACH_FUNCTION (node)
	for(node=cgraph_nodes;node;node=node->next)
	{
		/* Nodes without a body, and clone nodes are not interesting. */
		if (!gimple_has_body_p (node->decl) || node->clone_of)
			continue;

		push_cfun (DECL_STRUCT_FUNCTION (node->decl));

		fprintf (dump_file, "\n Function : %s", cgraph_node_name(node));
		basic_block bb;
		FOR_EACH_BB_FN (bb, cfun)
		{
			fprintf (dump_file, "\n\t BB : %d", bb->index);
			gimple_stmt_iterator gsi;
			/* Details of the bb iterator API's can be found in the file gimple-iterator.h */
			for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    			{
				gimple stmt = gsi_stmt (gsi);
				fprintf (dump_file, "\n\t\t Statement : ");
				print_gimple_stmt (dump_file, stmt, 0, 0);

				/* Verify if the statement is an assignment statement */
				if (gimple_code (stmt) == GIMPLE_ASSIGN)
				{
					print_assign_stmt_operands (stmt);

					print_assign_stmt_operator (stmt);
				}
			}
		}

		/* restoring the context by popping cfun. */
		pop_cfun ();
	}
	fprintf (dump_file, "\n-------------------------------------------------------------------\n");
}

