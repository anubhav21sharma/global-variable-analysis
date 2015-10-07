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
	//TODO: What about const global variables?
	return is_global_var(v) && DECL_P(v);
}

bool GlobalVarAnalysis::isBuiltInFunction(struct cgraph_node *node) {
	//TODO: Check whether function is a builtin
	//return DECL_IS_BUILTIN(node->decl);
	return true;
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
	struct cgraph_edge *edgei, *e;
	struct cgraph_edge *edge;
	for (node = cgraph_nodes; node; node = node->next) {
		if (!gimple_has_body_p(node->decl) || node->clone_of) {
			continue;
		}
		if (isBuiltInFunction(node)) {
			string fid = string(cgraph_node_name(node));
			Function f(fid, node);
			listOfFunctions.push_back(f);
			push_cfun(DECL_STRUCT_FUNCTION(node->decl));
			for (edge = node->callees; edge; edge = edge->next_callee) {
				Function calleeF(string(cgraph_node_name(edge->callee)), edge->callee);
				callGraph[f].insert(calleeF);
			}
			pop_cfun();
		}

	}
}

void GlobalVarAnalysis::collectDirectGlobalsInFunction() {
	for (int i = 0; i < listOfFunctions.size(); i++) {
		struct cgraph_node *node = listOfFunctions[i].fNode;
		push_cfun((function *) DECL_STRUCT_FUNCTION(node->decl));
		basic_block bb;
		FOR_EACH_BB_FN(bb, cfun)
		{
			gimple_stmt_iterator gsi;
			for (gsi = gsi_start_bb(bb); !gsi_end_p(gsi); gsi_next(&gsi)) {
				gimple curStmt = gsi_stmt(gsi);
				if (gimple_code(curStmt) == GIMPLE_ASSIGN) {
					int numOps = gimple_num_ops(curStmt);
					while (numOps--) {
						tree var = gimple_op(curStmt, numOps);
						if (true/*TREE_CODE(var) != INTEGER_CST || TREE_CODE(var) == VAR_DECL || TREE_CODE(var) == SSA_NAME || TREE_CODE(var) == PARM_DECL*/) {
							if (isGlobal(var)) {
								Variable v(varToString(var), var);
								directGlobalsInFunctions[listOfFunctions[i]].insert(v);
							}
						}
					}
				} else if (gimple_code(curStmt) == GIMPLE_CALL) {
					int nArgs = gimple_call_num_args(curStmt);
					while (nArgs--) {
						tree arg = gimple_call_arg(curStmt, nArgs);
						if (isGlobal(arg)) {
							Variable v(varToString(arg), arg);
							directGlobalsInFunctions[listOfFunctions[i]].insert(v);
						}
					}
				} else if (gimple_code(curStmt) == GIMPLE_RETURN) {
					//TODO: This condition does not seem to be doing anything.
					int nArgs = gimple_call_num_args(curStmt);
					if (nArgs == 1) {
						tree arg = gimple_call_arg(curStmt, nArgs);
						if (isGlobal(arg)) {
							Variable v(varToString(arg), arg);
							directGlobalsInFunctions[listOfFunctions[i]].insert(v);
						}
					}
				} else if (gimple_code(curStmt) == GIMPLE_COND) {
					tree varLHS = gimple_cond_lhs(curStmt);
					tree varRHS = gimple_cond_rhs(curStmt);
					if (isGlobal(varLHS)) {
						Variable v(varToString(varLHS), varLHS);
						directGlobalsInFunctions[listOfFunctions[i]].insert(v);
					}
					if (isGlobal(varRHS)) {
						Variable v(varToString(varRHS), varRHS);
						directGlobalsInFunctions[listOfFunctions[i]].insert(v);
					}
				} else {
					cerr << "Unhandled statement : " << "\t";
					print_gimple_stmt(stderr, curStmt, 0, 0);
					//cerr <<"\t File : "<<gimple_filename(curStmt)<<" Line : "<<gimple_lineno(curStmt)<<endl;
					cerr.flush();

				}
			}
		}

		pop_cfun();

	}
}

void GlobalVarAnalysis::collectIndirectGlobalsInFunction() {
	for(int i=0; i<listOfFunctions.size(); i++){
		Function f = listOfFunctions[i];
		set<Function> fr = reachabilities[f];
		for (set<Function>::iterator it = fr.begin(); it != fr.end(); it++) {
			Function g = *it;
			indirectGlobalsInFunctions[f].insert(directGlobalsInFunctions[g].begin(),directGlobalsInFunctions[g].end());
		}
		for (set<Variable>::iterator it = indirectGlobalsInFunctions[f].begin(); it != indirectGlobalsInFunctions[f].end(); it++) {
			if(directGlobalsInFunctions[f].find(*it) != directGlobalsInFunctions[f].end()){
				indirectGlobalsInFunctions[f].erase(*it);
			}
		}
	}
}

void GlobalVarAnalysis::findReachabilities() {
	int n = listOfFunctions.size();

	vector<vector<bool> > adjM(n, vector<bool>(n));
	for (int i = 0; i < n; i++)
		for (int j = 0; j < n; j++)
			adjM[i][j] = false;

	for (int i = 0; i < listOfFunctions.size(); i++) {
		set<Function> callees = callGraph[listOfFunctions[i]];
		for (set<Function>::iterator it = callees.begin(); it != callees.end(); it++) {
			int j = linearSearch(listOfFunctions, *it);
			adjM[i][j] = true;
		}
	}
	for (int k = 0; k < n; k++) {
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				adjM[i][j] = adjM[i][j] || (adjM[i][k] && adjM[k][j]);
			}
		}
	}

	//TODO: Might be wrong. Confirm.
	for (int i = 0; i < n; i++) {
		Function f = listOfFunctions[i];
		for (int j = 0; j < n; j++) {
			if (adjM[i][j]) {
				reachabilities[f].insert(listOfFunctions[j]);
			}
		}
	}

}

