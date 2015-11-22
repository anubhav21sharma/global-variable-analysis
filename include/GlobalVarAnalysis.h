/*
 * GlobalVarAnalysis.h
 *
 *  Created on: 30-Sep-2015
 *      Author: anubhav
 */

#ifndef GLOBALVARANALYSIS_H_
#define GLOBALVARANALYSIS_H_

#include <iostream>
#include <map>
#include <vector>
#include <string>
#include <set>
#include "../include/Variable.h"
#include "../include/Function.h"

#include "gcc-plugin.h"
#include "tree.h"
#include "basic-block.h"
#include "tree-ssa-alias.h"
#include "gimple.h"
#include "cgraph.h"
#include "tree-pass.h"
#include "gimple-pretty-print.h"

class GlobalVarAnalysis {
public:
	std::vector<Variable> listOfGlobalVars;
	std::vector<Function> listOfFunctions;
	std::map<Function, std::set<Variable> > directGlobalsInFunctions;
	std::map<Function, std::set<Variable> > indirectGlobalsInFunctions;
	std::map<Function, std::set<Variable> > directAndIndirectGlobalsInFunctions;
	std::map<Variable, std::set<Variable> > pointsToInformation;
	std::map<Function, std::set<Function> > callGraph;
	std::map<Function, std::set<Function> > reachabilities;
	GlobalVarAnalysis();
	void collectAllGlobals();
	void populateFunctionIDs();
	void findReachabilities();
	void collectDirectGlobalsInFunction();
	void collectIndirectGlobalsInFunction();
	void collectPointsToInformation();
	bool isGlobal(tree);
	bool isBuiltInFunction(struct cgraph_node*);
	virtual ~GlobalVarAnalysis();
};

#endif /* GLOBALVARANALYSIS_H_ */
