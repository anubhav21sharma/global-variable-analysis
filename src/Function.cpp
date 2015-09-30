/*
 * Function.cpp
 *
 *  Created on: 30-Sep-2015
 *      Author: anubhav
 */

#include "../include/Function.h"

using namespace std;

Function::Function() {
}

Function::Function(string fid, cgraph_node* fNode) {
	this->fId = fid;
	this->fNode = fNode;
}

Function::~Function() {
}
