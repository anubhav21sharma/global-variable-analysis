/*
 * Variable.cpp
 *
 *  Created on: 30-Sep-2015
 *      Author: anubhav
 */
#include "../include/Variable.h"

using namespace std;
Variable::Variable(){
	varName = "";
	varTree = NULL;
}

Variable::Variable(string varName, tree varTree){
	this->varName = varName;
	this->varTree = varTree;
}

Variable::~Variable(){

}
