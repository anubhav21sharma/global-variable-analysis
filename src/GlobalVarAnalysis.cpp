/*
 * GlobalVarAnalysis.cpp
 *
 *  Created on: 30-Sep-2015
 *      Author: anubhav
 */

#include "../include/GlobalVarAnalysis.h"

#include <sstream>

#include "../include/Common.h"

using namespace std;

#define intToString(x) dynamic_cast< std::ostringstream & >(( std::ostringstream() << std::dec << x ) ).str()

GlobalVarAnalysis::GlobalVarAnalysis() {

}

bool GlobalVarAnalysis::isGlobal(tree v) {
	return is_global_var(v) && DECL_P(v);
}

GlobalVarAnalysis::~GlobalVarAnalysis() {
}

void GlobalVarAnalysis::collectAllGlobals() {
	struct varpool_node *node;
	for (node = varpool_nodes; node; node = node->next) {
		tree tVar = node->decl;
		if (!DECL_ARTIFICIAL(tVar)) {
			string varName = string(get_name(tVar));
			Variable v(varName, tVar);
			listOfGlobalVars.push_back(v);
		}
	}
}

void GlobalVarAnalysis::populateFunctionIDs() {
	struct cgraph_node *node;
	for (node = cgraph_nodes; node; node = node->next) {
		string fid = string(cgraph_node_name(node));
		Function f(fid, node);
		listOfFunctions.push_back(f);
	}
}
//DECL_BUILT_IN
void GlobalVarAnalysis::collectGlobalsInFunction() {
	for (int i = 0; i < listOfFunctions.size(); i++) {
		struct cgraph_node *node = listOfFunctions[i].fNode;
		push_cfun((function *) DECL_STRUCT_FUNCTION(node->decl));
		basic_block bb;
		FOR_EACH_BB_FN (bb, cfun)
		{
			gimple_stmt_iterator gsi;
			for (gsi = gsi_start_bb(bb); !gsi_end_p(gsi); gsi_next(&gsi)) {
				gimple curStmt = gsi_stmt(gsi);
				if (gimple_code(curStmt) == GIMPLE_ASSIGN) {
					int numOps = gimple_num_ops(curStmt);
					while (numOps--) {
						tree var = gimple_op(curStmt, numOps);
						if (TREE_CODE(var) != INTEGER_CST/*TREE_CODE(var) == VAR_DECL || TREE_CODE(var) == SSA_NAME || TREE_CODE(var) == PARM_DECL*/) {
							if (isGlobal(var)) {
								Variable v(varToString(var), var);
								globalsInFunctions[listOfFunctions[i]].insert(v);
							}

						}

					}
				} else if (gimple_code(curStmt) == GIMPLE_COND) {
					int numOps = gimple_num_ops(curStmt);
					while (numOps--) {
						tree var = gimple_op(curStmt, numOps);
						if (TREE_CODE(var) != INTEGER_CST/*TREE_CODE(var) == VAR_DECL || TREE_CODE(var) == SSA_NAME || TREE_CODE(var) == PARM_DECL*/) {
							if (isGlobal(var)) {
								Variable v(varToString(var), var);
								globalsInFunctions[listOfFunctions[i]].insert(v);
							}

						}

					}
				}

			}
		}

		pop_cfun();

	}
}

