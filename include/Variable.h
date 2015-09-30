/*
 * Variable.h
 *
 *  Created on: 30-Sep-2015
 *      Author: anubhav
 */

#include <string>
#include "gcc-plugin.h"
#include "tree.h"

#ifndef VARIABLE_H_
#define VARIABLE_H_

class Variable {
public:
	std::string varName;
	tree varTree;
	Variable();
	Variable(std::string, tree);

	bool operator <(const Variable& v2) const {
		return varName < v2.varName;
	}


	virtual ~Variable();
};

#endif /* VARIABLE_H_ */
