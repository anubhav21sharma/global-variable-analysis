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

#include "../include/GlobalVarAnalysis.h"

#include <iostream>

using namespace std;

/* global declarations */
static unsigned int execute_gimple_manipulation(void);

/*-----------------------------------------------------------------------------
 *  Each plugin MUST define this global int to assert compatibility with GPL; 
 *  else the compiler throws a fatal error 
 *-----------------------------------------------------------------------------*/
int plugin_is_GPL_compatible;

/*-----------------------------------------------------------------------------
 *  Structure of the pass we want to insert, identical to a regular ipa pass
 *-----------------------------------------------------------------------------*/
struct simple_ipa_opt_pass myPass = { { SIMPLE_IPA_PASS,	//  opt type name
"demo",							//  name
0,                             //  gate
execute_gimple_manipulation,   //  execute function
NULL, /*  sub */
NULL, /*  next */
0, /*  static pass number */
TV_INTEGRATION, /*  tv_id */
0, /*  properties required */
0, /*  properties provided */
0, /*  properties destroyed */
0, /*  todo_flags start */
0 /*  todo_flags end */
} };

/*-----------------------------------------------------------------------------
 *    This structure provides the information about inserting the pass in the
 *    pass manager. 
 *-----------------------------------------------------------------------------*/
struct register_pass_info pass_info = { &(myPass.pass), /* Address of new pass, here, the 'struct opt_pass' field of 'simple_ipa_opt_pass'
 defined above */
"pta", /* Name of the reference pass for hooking up the new pass.  */

0, /* Insert the pass at the specified instance number of the reference pass.
 Do it for every instance if it is 0. */

PASS_POS_INSERT_AFTER /* how to insert the new pass: before, after, or replace. Here we are inserting
 a pass names 'plug' after the pass named 'pta' */
};

int breakPointMethod() {
	return 0;
}

extern int plugin_init(struct plugin_name_args* plugin_info, struct plugin_gcc_version* version) {
	breakPointMethod();
	register_callback(plugin_info->base_name, /* char *name: Plugin name, could be any
	 name. plugin_info->base_name gives this filename */
	PLUGIN_PASS_MANAGER_SETUP, /* int event: The event code. Here, setting up a new pass */
	NULL, /* The function that handles event */
	&pass_info); /* plugin specific data */

	return 0;

}

/* ---------------------------------------------
 The main driver function to perform analysis.
 ---------------------------------------------*/
static unsigned int execute_gimple_manipulation(void) {

	if (!dump_file) {
		//dump_file = stdout;
	}
	//dump_file = stdout;
	GlobalVarAnalysis gvAnalysis;
	gvAnalysis.collectAllGlobals();
	gvAnalysis.populateFunctionIDs();
	gvAnalysis.findReachabilities();
	gvAnalysis.collectDirectGlobalsInFunction();
	gvAnalysis.collectIndirectGlobalsInFunction();

	cout << endl << "All Global Vars:" << endl;
	for (std::vector<Variable>::iterator it = gvAnalysis.listOfGlobalVars.begin(); it != gvAnalysis.listOfGlobalVars.end(); it++) {
		cout << it->varName << ",";
	}

	cout << endl<<endl << "All Functions:" << endl;
	for (std::vector<Function>::iterator it = gvAnalysis.listOfFunctions.begin(); it != gvAnalysis.listOfFunctions.end(); it++) {
		cout << it->fId << endl;
	}

	cout << endl << "Call Graph:" << endl;
	for (std::vector<Function>::iterator it = gvAnalysis.listOfFunctions.begin(); it != gvAnalysis.listOfFunctions.end(); it++) {
		cout << it->fId << " : ";
		set<Function> sCallees = gvAnalysis.callGraph[*it];
		for (std::set<Function>::iterator it2 = sCallees.begin(); it2 != sCallees.end(); it2++) {
			cout << it2->fId << ", ";
		}
		cout << endl;
	}

	cout << endl << "Reachabilities:" << endl;
	for (std::vector<Function>::iterator it = gvAnalysis.listOfFunctions.begin(); it != gvAnalysis.listOfFunctions.end(); it++) {
		cout << it->fId << " : ";
		set<Function> reachableFunctions = gvAnalysis.reachabilities[*it];
		for (std::set<Function>::iterator it2 = reachableFunctions.begin(); it2 != reachableFunctions.end(); it2++) {
			cout << it2->fId << ", ";
		}
		cout << endl;
	}

	cout << endl << "Function to Direct Globals Map:" << endl;
	for (std::vector<Function>::iterator it = gvAnalysis.listOfFunctions.begin(); it != gvAnalysis.listOfFunctions.end(); it++) {
		cout << it->fId << " : ";
		set<Variable> svars = gvAnalysis.directGlobalsInFunctions[*it];
		for (std::set<Variable>::iterator it2 = svars.begin(); it2 != svars.end(); it2++) {
			cout << it2->varName << ", ";
		}
		cout << endl;
	}

	cout << endl << "Function to Indirect Globals Map:" << endl;
	for (std::vector<Function>::iterator it = gvAnalysis.listOfFunctions.begin(); it != gvAnalysis.listOfFunctions.end(); it++) {
		cout << it->fId << " : ";
		set<Variable> svars = gvAnalysis.indirectGlobalsInFunctions[*it];
		for (std::set<Variable>::iterator it2 = svars.begin(); it2 != svars.end(); it2++) {
			cout << it2->varName << ", ";
		}
		cout << endl;
	}

	return 0;
}
