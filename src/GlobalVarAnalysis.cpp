/*
 * GlobalVarAnalysis.cpp
 *
 *  Created on: 30-Sep-2015
 *      Author: anubhav
 */

#include "../src/Points_to4.hpp"
#include "../include/GlobalVarAnalysis.h"
#include <sstream>
#include "../include/Common.h"
#include "../src/parser.hpp"

using namespace std;
extern Allptsinfo execute_ipacs();

#define intToString(x) dynamic_cast< std::ostringstream & >(( std::ostringstream() << std::dec << x ) ).str()

bool printAllStatementInfo = true;

GlobalVarAnalysis::GlobalVarAnalysis() {

}

bool GlobalVarAnalysis::isGlobal(tree v) {
	//TODO: What about const global variables?
	return is_global_var(v) && DECL_P(v);
}

bool GlobalVarAnalysis::isBuiltInFunction(struct cgraph_node *node) {
	//TODO: Check whether function is a builtin
	//return DECL_IS_BUILTIN(node->decl);
	return false;
}

GlobalVarAnalysis::~GlobalVarAnalysis() {
}

void GlobalVarAnalysis::collectPointsToInformation() {
	Allptsinfo allPointsInfo = execute_ipacs();
	for (map<int, PSet>::iterator it = allPointsInfo.allptinfo.begin(); it != allPointsInfo.allptinfo.end(); it++) {
		int pointer_id = it->first;
		csvarinfo_t pointer = VEC_index(csvarinfo_t, csvarmap, pointer_id);
		tree pvar = pointer->decl;
		if (pvar == NULL)
			continue;
		if (!(is_global_var(pvar) && DECL_P(pvar))) {
			//continue;
		}
		if (pointer->name == NULL) {
			//Should not happen
			continue;
		}
		Variable key(string(pointer->name), pvar);

		Pointee_Set pointee_set = it->second.get_st();
		for (set<int>::iterator it = pointee_set.begin(); it != pointee_set.end(); it++) {
			csvarinfo_t var = VEC_index(csvarinfo_t, csvarmap, *it);
			if (var->decl == NULL)
				continue;
			string varName;
			if (get_name(var->decl) == NULL) {
				//Should not happen
				continue;
			}
			varName = string(get_name(var->decl));
			Variable pointee(varName, var->decl);
			pointsToInformation[key].insert(pointee);
		}
	}
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
		if (!isBuiltInFunction(node)) {
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

/*
 * if(OPi is a pointer){
 * 		if(OPi is dereferenced){
 * 			add OPi, A(OPi);
 * 		}else{
 * 			add OPi;
 * 		}
 * }
 */
// How to find names of vars *px;
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
				if (printAllStatementInfo) {
					cout << "\nStatement:";
					print_gimple_stmt(stdout, curStmt, 0, 0);
				}
				if (gimple_code(curStmt) == GIMPLE_ASSIGN) {
					int numOps = gimple_num_ops(curStmt);
					while (numOps--) {
						tree var = gimple_op(curStmt, numOps);
						if (printAllStatementInfo) {
							cout << "Var=" << varToString(var) << endl;
							cout << "isGlobal = " << isGlobal(var) << endl;
							cout << "code=" << TREE_CODE(var) << endl;
						}
						if (isGlobal(var)) {
							//If pointer is a global variable. (Seems like this case won't happen)
							string varName = varToString(var);
							if (TREE_CODE(var) == MEM_REF || TREE_CODE(var) == TARGET_MEM_REF || TREE_CODE(var) == ARRAY_REF) {
								tree deref = TREE_OPERAND(var, 0);
								varName = varToString(deref);
								var = deref;
								if (printAllStatementInfo) {
									cout << "GVar=" << varName << endl;
								}
							}
							Variable v(varName, var);
							directGlobalsInFunctions[listOfFunctions[i]].insert(v);
						} else {
							//Check whether variable is a pointer and add globals from pointee set.
							string varName = varToString(var);
							if (TREE_CODE(var) == MEM_REF || TREE_CODE(var) == TARGET_MEM_REF) {
								tree deref = TREE_OPERAND(var, 0);
								deref = SSA_NAME_VAR(deref);
								varName = varToString(deref);
								Variable pointer(varName, deref);
								set<Variable> pointees = pointsToInformation[pointer];

								for (std::set<Variable>::iterator it = pointees.begin(); it != pointees.end(); it++) {
									if (isGlobal(it->varTree)) {
										//cout << "Adding global pointee = " << it->varName << endl;
										directGlobalsInFunctions[listOfFunctions[i]].insert(*it);
									}
								}
//									cout << "Var=" << varName << endl;
							} else if (TREE_CODE(var) == ADDR_EXPR) {
								tree deref = TREE_OPERAND(var, 0);
								varName = varToString(deref);
								Variable v(varName, deref);
								if (isGlobal(deref)) {
									directGlobalsInFunctions[listOfFunctions[i]].insert(v);
								}
//									cout << "Var=" << varName << endl;
							} else if (TREE_CODE(var) == ARRAY_REF) {
								tree deref = TREE_OPERAND(var, 0);
								while (TREE_CODE(deref) == COMPONENT_REF || TREE_CODE(deref) == ARRAY_REF) {
									deref = TREE_OPERAND(deref, 0);
								}
								varName = varToString(deref);
								Variable v(varName, deref);
								if (isGlobal(deref)) {
									directGlobalsInFunctions[listOfFunctions[i]].insert(v);
								}
							} else if (TREE_CODE(var) == COMPONENT_REF) {
								tree deref = TREE_OPERAND(var, 0);
								while (TREE_CODE(deref) == COMPONENT_REF || TREE_CODE(deref) == ARRAY_REF) {
									deref = TREE_OPERAND(deref, 0);
								}
								varName = varToString(deref);
								Variable v(varName, deref);
								if (isGlobal(deref)) {
									directGlobalsInFunctions[listOfFunctions[i]].insert(v);
								}
							}
						}

					}
				} else if (gimple_code(curStmt) == GIMPLE_CALL) {
					int nArgs = gimple_call_num_args(curStmt);

					while (nArgs--) {
						tree arg = gimple_call_arg(curStmt, nArgs);
						if (printAllStatementInfo) {
							cout << "Var=" << varToString(arg) << endl;
							cout << "isGlobal = " << isGlobal(arg) << endl;
							cout << "code=" << TREE_CODE(arg) << endl;
						}
						if (TREE_CODE(arg) == COMPONENT_REF || TREE_CODE(arg) == ARRAY_REF) {
							tree deref = TREE_OPERAND(arg, 0);
							while (TREE_CODE(deref) == COMPONENT_REF || TREE_CODE(deref) == ARRAY_REF) {
								deref = TREE_OPERAND(deref, 0);
							}
							string varName = varToString(deref);
							Variable v(varName, deref);
							if (isGlobal(deref)) {
								directGlobalsInFunctions[listOfFunctions[i]].insert(v);
							}
						} else if (TREE_CODE(arg) == ADDR_EXPR) {
							tree deref = TREE_OPERAND(arg, 0);
							string varName = varToString(deref);
							Variable v(varName, deref);
							if (isGlobal(deref)) {
								directGlobalsInFunctions[listOfFunctions[i]].insert(v);
							}
						} else {
							if (isGlobal(arg)) {
								Variable v(varToString(arg), arg);
								directGlobalsInFunctions[listOfFunctions[i]].insert(v);
							}
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
				} else if (gimple_code(curStmt) == GIMPLE_SWITCH) {
					int numOps = gimple_num_ops(curStmt);
					while (numOps--) {
						tree var = gimple_op(curStmt, numOps);
						if (isGlobal(var)) {
							Variable v(varToString(var), var);
							directGlobalsInFunctions[listOfFunctions[i]].insert(v);
						}
					}
				} else {
					if (gimple_code(curStmt) == GIMPLE_LABEL || gimple_code(curStmt) == GIMPLE_ASM || gimple_code(curStmt) == GIMPLE_NOP || gimple_code(curStmt) == GIMPLE_RESX) {

					} else {
						cout << "Unhandled statement : " << "\t";
						print_gimple_stmt(stdout, curStmt, 0, 0);
						//cout << "\t File : " << gimple_filename(curStmt) << " Line : " << gimple_lineno(curStmt) << endl;
					}
				}
			}
		}

		pop_cfun();

	}
}

void GlobalVarAnalysis::collectIndirectGlobalsInFunction() {
	for (int i = 0; i < listOfFunctions.size(); i++) {
		Function f = listOfFunctions[i];
		set<Function> fr = reachabilities[f];
		for (set<Function>::iterator it = fr.begin(); it != fr.end(); it++) {
			Function g = *it;
			indirectGlobalsInFunctions[f].insert(directGlobalsInFunctions[g].begin(), directGlobalsInFunctions[g].end());
		}
		for (set<Variable>::iterator it = indirectGlobalsInFunctions[f].begin(); it != indirectGlobalsInFunctions[f].end(); it++) {
			if (directGlobalsInFunctions[f].find(*it) != directGlobalsInFunctions[f].end()) {
				directAndIndirectGlobalsInFunctions[f].insert(*it);
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
			if (j != -1)
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

	for (int i = 0; i < n; i++) {
		Function f = listOfFunctions[i];
		for (int j = 0; j < n; j++) {
			if (adjM[i][j]) {
				reachabilities[f].insert(listOfFunctions[j]);
			}
		}
	}

}

/*//
 //								tree type = TREE_TYPE(var);
 //								cout << "Type of Var = " << varToString(var) << ": " << TREE_CODE(type) << endl;
 //								cout << "Code of Var = " << varToString(var) << ": " << TREE_CODE(var) << endl;
 //								if (TREE_CODE(var) == MEM_REF) {
 //									cout << "*" << varToString(var) << endl;
 //								}
 cout << "\nStatement:";
 print_gimple_stmt(stdout, curStmt, 0, 0);
 constraint_t con;
 int lhs_type, rhs_type;
 int lhs_var_id, rhs_var_id;
 for (int i = 0;
 i < VEC_length(constraint_t, aliases);
 i++) {
 con = VEC_index(constraint_t, aliases, i);

 lhs_type = con->lhs.type;
 rhs_type = con->rhs.type;
 lhs_var_id = con->lhs.var;
 rhs_var_id = con->rhs.var;

 csvarinfo_t lhs_pointer = VEC_index(csvarinfo_t, csvarmap, con->lhs.var);
 csvarinfo_t rhs_pointer = VEC_index(csvarinfo_t, csvarmap, con->rhs.var);
 if (1) {
 cout << "lhs->decl " << varToString(lhs_pointer->decl) << endl;
 cout << "lhsTree " << varToString(lhsTree) << endl;
 cout << "LHS NAME =" << lhs_pointer->name << endl;
 cout << "RHS NAME =" << rhs_pointer->name << endl;
 //cout << "TYPE = " << lhs_type << "," << rhs_type << endl;
 }

 }
 //*/
