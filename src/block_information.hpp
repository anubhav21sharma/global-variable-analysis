#ifndef BLOCK_INFORMATION_H
#define BLOCK_INFORMATION_H

#include "dataflow.hpp"
//#include "parser.hpp"
#include "gcc-plugin.h"
#include "config.h"
#include "system.h"
#include "cgraph.h"
#include "coretypes.h"
#include "tm.h"
#include "tree.h"
#include "tree-flow.h"
#include "diagnostic.h"
#include "tree-pass.h"
#include "timevar.h"
#include "alloc-pool.h"
#include "params.h"
#include "ggc.h"
#include "vec.h"
#include "gimple-pretty-print.h"
#include<iostream>
#include "con.hpp"
#include <vector>
#include<list>
#include<set>

using namespace std;

class block_information {

	struct cgraph_node * node;
	constraint_list cons;
	DVG points_in, points_out;
	live_info live_in, live_out;
	DVG d_in, d_out;
	DVG summ;

public:

	map<edge_id, unsigned int> order_in;
	map<edge_id, unsigned int> order_out;

	bool call_block;
	bool return_block;
	bool start_block;
	bool end_block;
	int linitialized;
	int pinitialized;
	int dinitialized;

public:

	block_information() {
		call_block = false;
		return_block = false;
		start_block = false;
		end_block = false;
		linitialized = 1;
		pinitialized = 1;
		dinitialized = 1;
	}
	block_information(struct cgraph_node *);
	constraint_list & get_list();
	struct cgraph_node * get_cfun();

	//functions for pointer information
	DVG get_d_in();
	DVG get_d_out();

	DVG get_summ();
	void set_summ(DVG);

	void set_d_in(DVG);
	void set_d_out(DVG);

	DVG get_points_in();
	DVG get_points_out();

	void set_points_in(DVG g);
	void set_points_out(DVG g);

	//============================================

	//functions for liveness information in map
	live_info get_live_in();
	live_info get_live_out();

	void set_live_in(live_info);
	void set_live_out(live_info);

};

#endif

