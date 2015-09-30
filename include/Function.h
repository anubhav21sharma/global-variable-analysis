/*
 * Function.h
 *
 *  Created on: 30-Sep-2015
 *      Author: anubhav
 */

#ifndef FUNCTION_H_
#define FUNCTION_H_

#include "gcc-plugin.h"
#include "cgraph.h"
#include <string>

class Function {
public:
	std::string fId;
	cgraph_node *fNode;
	Function();
	Function(std::string, cgraph_node*);
	bool operator <(const Function& f2) const {
		return fId < f2.fId;
	}
	bool operator >(const Function& f2) const {
		return fId > f2.fId;
	}
	virtual ~Function();
};

#endif /* FUNCTION_H_ */
