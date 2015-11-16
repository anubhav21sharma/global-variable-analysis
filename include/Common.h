/*
 * Common.h
 *
 *  Created on: 30-Sep-2015
 *      Author: anubhav
 */

#ifndef COMMON_H_
#define COMMON_H_

#include "gcc-plugin.h"
#include "tree.h"
#include "tree-flow.h"
#include "basic-block.h"
#include "tree-ssa-alias.h"
#include "gimple.h"
#include "cgraph.h"
#include "tree-pass.h"
#include "gimple-pretty-print.h"
#include <string>
#include <vector>
#include "Function.h"
#include <string.h>
#include <iostream>
#include <exception>

using namespace std;

int linearSearch(vector<Function> v, Function f) {
	for (int i = 0; i < v.size(); i++) {
		if (v[i].fId == f.fId)
			return i;
	}
	return -1;
}

string stmtToString(gimple stmt) {
	char* buffer;
	size_t len;
	FILE* fp = open_memstream(&buffer, &len);
	print_gimple_stmt(fp, stmt, 0, 0);
	fprintf(fp, "\0");
	string str_stmt(buffer);
	return str_stmt;
}

std::string varToString(tree node) {

	if (node == NULL) {
		return "NULL";
	}
	char* name = new char[40];
	tree var_decl_node = node;
	try {
		if (TREE_CODE(node) == SSA_NAME) {
			var_decl_node = SSA_NAME_VAR(node);
		}
		if (TREE_CODE(node) == ARRAY_REF || TREE_CODE(node) == MEM_REF || TREE_CODE(node) == ADDR_EXPR) {
			var_decl_node = node;
			while ( TREE_CODE(var_decl_node) != VAR_DECL && TREE_CODE(var_decl_node) != STRING_CST && TREE_CODE(var_decl_node) != FUNCTION_DECL && TREE_CODE(var_decl_node) != SSA_NAME && TREE_CODE(var_decl_node) != PARM_DECL)
				var_decl_node = TREE_OPERAND(var_decl_node, 0);
		}
		if (DECL_NAME(var_decl_node)) {
			const char* varName = get_name(var_decl_node);
			if (varName != NULL) {
				strcpy(name, varName);
			}
		} else {
			char *temp = new char[10];
			strcpy(name, "D.");
			sprintf(temp, "%d", DECL_UID(var_decl_node));
			strcat(name, temp);
		}
		if (TREE_CODE(node) == SSA_NAME) {
			strcat(name, "_");
			char *ver = new char[10];
			sprintf(ver, "%d", SSA_NAME_VERSION(node));
			strcat(name, ver);
		}
	} catch (exception& e) {
		cerr << "Exception varToString: " /*<< e.what()*/ << endl;
	}
	return std::string(name);
}

#endif
