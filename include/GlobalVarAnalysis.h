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
	std::map<Function, std::set<Variable> > globalsInFunctions;
	GlobalVarAnalysis();
	void collectAllGlobals();
	void populateFunctionIDs();
	void collectGlobalsInFunction();
	bool isGlobal(tree);

	virtual ~GlobalVarAnalysis();
};

#endif /* GLOBALVARANALYSIS_H_ */
