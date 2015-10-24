#ifndef CGRAPH_NODE_H
#define CGRAPH_NODE_H

#include "dataflow.hpp"
#include "parser.hpp"
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
#include<stack>
#include<list>
#include<map>
#include<set>

#define BLOCK_COUNT 5000

using namespace std;

class function_info {

	private:
	      bool visited;
	      bool dvisited;

	      DVG flow_insens;
	      DVG prev_dvg;		

	      map<unsigned int, set_edges> order_map;	
	      map<edge_id, unsigned int> rev_order_map;	

	      set<unsigned int> params;
	      unsigned int ret_id;	

	      unsigned int num_bb;	
	      unsigned int end_block_index;

	      bool has_ret;

	      unsigned int pred_count;	
	      int reach;
	      unsigned int inter_order;	
	      bool marked;
	
        public:
		map< unsigned int, set_edges > orig_order_map;
		map< edge_id, unsigned int > orig_rev_order_map;

		set< unsigned int > trans_callees;

		set_call_pts call_pts;
		unsigned int max_depth;

	      unsigned int ret_bb;	
		unsigned int end_block_id;

     	      unsigned int callee_count;
	      unsigned int cons_num;	
	      unsigned int call_num;	

	      DVG get_prev_dvg();
	      void set_prev_dvg(DVG);	
	
	      int rev_post_order[BLOCK_COUNT];	
	      int post_order[BLOCK_COUNT];	
	      int bb_rp_order[BLOCK_COUNT];	
	      int bb_p_order[BLOCK_COUNT];	

	      bool live_worklist[BLOCK_COUNT];	
	      bool points_worklist[BLOCK_COUNT];	

              bool ordered;

	      unsigned int func_num;	
		
	      set< unsigned int > call_block_list;
	      unsigned int count;
	      unsigned int use_count;		
	      unsigned int dcount;	

              function_info() {dvisited = false; visited = false; has_ret = false;count = 0; ordered  = false; pred_count = 0; reach = 0; inter_order = 0; marked = false; callee_count = 0; call_num = 0; cons_num = 0; dcount = 0; use_count = 0; end_block_id = 0; max_depth = 0;}

	      unsigned int get_pred_count();
	      void set_pred_count(unsigned int);

	      unsigned int get_reach();
	      void set_reach(unsigned int);

	      unsigned int get_inter_order();
	      void set_inter_order(unsigned int);

	      bool is_marked();
	      void set_marked();	
	      void reset_marked();	

	      bool is_visited();
	      void set_visited(bool b);

	      bool is_dvisited();
	      void set_dvisited(bool b);

	      unsigned int get_num_bb();
	      void set_num_bb(unsigned int);

	      unsigned int get_end_block_index();
	      void set_end_block_index(unsigned int);

	      bool has_ret_type();
	      void set_ret_type();
	      void reset_ret_type();

//	      bool * get_live_worklist();
//	      bool * get_points_worklist();

//	      void set_live_worklist(bool *);	
//	      void set_points_worklist(bool *);	

	      bool is_empty_worklist(int);

//	      int * get_rev_post_order();	
//	      int * get_bb_order();	

//	      void set_rev_post_order(int *);	
//	      void set_bb_order(int *);	

	      map<unsigned int, set_edges> get_order_map();
	      void set_order_map(map<unsigned int, set_edges>);	

	      map<edge_id, unsigned int> get_rev_order_map();
	      void set_rev_order_map(map<edge_id, unsigned int>);	

	      set_edges get_edges_order(unsigned int);
              void set_edges_order(unsigned int, set_edges);

	      unsigned int get_order_edge(edge_id i);
              void set_order_edge(unsigned int o, edge_id i);

	      set<unsigned int> get_params();
	      void set_params(set<unsigned int> p);

	      void add_param(unsigned int);
		
	      unsigned int get_ret_id();
	      void set_ret_id(unsigned int);	

	      DVG get_fi_dvg();
	      void set_fi_dvg(DVG);		
	      	
};

extern map< unsigned int, struct cgraph_node * > func_numbering;

#endif
