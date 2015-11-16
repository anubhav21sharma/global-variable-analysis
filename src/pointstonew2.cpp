#include "dataflow.hpp"
#include "parser.hpp"
#include "block_information.hpp"
#include "cgraph_node.hpp"
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
#include<time.h>
#include "con.hpp"
#include<map>
/**************************/
#include "Points_to4.hpp"
/*************************/
#define alloc_mem ggc_alloc_cleared_atomic 
#define DATA 0
#define total_bbs n_basic_blocks-NUM_FIXED_BLOCKS

using namespace std;

/*-----------------------------------------------------------------------------
 *  Each plugin MUST define this global int to assert compatibility with GPL; 
 *  else the compiler throws a fatal error 
 *-----------------------------------------------------------------------------*/
//int plugin_is_GPL_compatible;
//clock_t start, end;
typedef vector<struct cgraph_node *>::iterator func_it;

set_cnodes cnodes_list_callers;

unsigned int iter = 1;

struct cgraph_node *gcnode;

double cpu_time_used;
int t = 0;
int c = 0;
int number_of_calls = 0;

double liveness_time_s = 0;
double points_to_time_s = 0;

//double liveness_time_d = 0;
double points_to_time_d = 0;

double ttime;

unsigned int func_ptr_count = 0;

void print_constraint_basic_block() {
	struct cgraph_node *cnode;
	gimple_stmt_iterator gsi;
	gimple stmt;
	basic_block bb;

//        constraint_expr_type 
	int lhs_type, rhs_type;
	int lhs_var_id, rhs_var_id;
	const char *lhs_op, *rhs_op;
	csvarinfo_t lhs, rhs;

	for (cnode = cgraph_nodes; cnode; cnode = cnode->next) {

		if (!gimple_has_body_p(cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION(cnode->decl));
		fprintf(dump_file, "\n============================================================================\n");
		fprintf(dump_file, "\n %s\n", cgraph_node_name(cnode));
		fprintf(dump_file, "\n============================================================================\n");

		FOR_EACH_BB(bb)
		{
			it ai;
			for (ai = ((block_information *) (bb->aux))->get_list().begin(); ai != ((block_information *) (bb->aux))->get_list().end(); ai++) {
				if (!(*ai).get_bool()) {
					fprintf(dump_file, "\nConstraint - Use\n");

					fprintf(dump_file, "\nBasic Block %d Constraint %d\n", bb->index, (*ai).get_int());
					lhs_op = VEC_index(csvarinfo_t,csvarmap,(*ai).get_int())->name;

					fprintf(dump_file, "\nOp: %s\n", lhs_op);

					continue;
				}
				((function_info *) (cnode->aux))->cons_num++;

//				fprintf(dump_file, "\nIn loop iteration no %d\n", i++);
				constraint_t con = VEC_index(constraint_t, aliases, (*ai).get_int());
				lhs_type = con->lhs.type;
//				fprintf(dump_file, "\nIn loop \n");
				rhs_type = con->rhs.type;
				lhs_var_id = con->lhs.var;
				rhs_var_id = con->rhs.var;
				lhs = VEC_index(csvarinfo_t, csvarmap, lhs_var_id);
				rhs = VEC_index(csvarinfo_t, csvarmap, rhs_var_id);
				unsigned int lhs_off = con->lhs.offset;
				unsigned int rhs_off = con->rhs.offset;
				lhs_op = lhs->name;
				rhs_op = rhs->name;
				fprintf(dump_file, "\nBasic Block %d Constraint %d\n", bb->index, (*ai).get_int());
				fprintf(dump_file, "\nLHS Op: %s LHS type: %d LHS Offset: %d\n RHS Op: %s RHS type: %d RHS Offset: %d\n", lhs_op, lhs_type, lhs_off, rhs_op, rhs_type, rhs_off);
//		                fprintf(dump_file,"\nLHS Variable Offset %d Size %d Full Size %d Flag %d\n", lhs->offset, lhs->size, lhs->fullsize,lhs->is_full_var);
//                		fprintf(dump_file,"\nRHS Variable Offset %d Size %d Full Size %d Flag %d\n", rhs->offset, rhs->size, rhs->fullsize, rhs->is_full_var);
			}
		}
		pop_cfun();
	}

}

void get_dfv_ppt() {
	struct cgraph_node *cnode;
	basic_block bb;
	DVG dfv;
	set_edges edges;

//	for (cnode=cgraph_nodes; cnode; cnode=cnode->next) 
	for (int k = 1; k < func_count; k++) {
		cnode = func_numbering[index_func_array[k]];

		if (!gimple_has_body_p(cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION(cnode->decl));

		FOR_EACH_BB(bb)
		{
			dfv = ((block_information *) (bb->aux))->get_d_in();
			edges = dfv.get_edge_list();
			fprintf(dump_file, "\nDFV Size for BB %d of Fn %d = %d\n", bb->index, cnode->uid, edges.size());
		}

		pop_cfun();
	}
}

DVG get_in_points_to_info(basic_block bb, struct cgraph_node *cnode) {
	edge e;
	edge_iterator ei;
	int i;

	DVG g;

	map<edge_id, unsigned int> temp_map, local_map;
	map<edge_id, unsigned int>::iterator mit;

	if (((block_information *) (bb->aux))->start_block) {
//		fprintf(dump_file,"\nStart Block %d Function %s", bb->index, cgraph_node_name(cnode));
		return ((block_information *) (bb->aux))->get_points_in();
	}

	vector<DVG> dvg_list;
//	i = 0;

	FOR_EACH_EDGE(e,ei,bb->preds)
	{
//		fprintf(dump_file,"\nBasic Block %d\n", bb->index);
		basic_block bt = e->src;

//		fprintf(dump_file,"\nSuccessor Basic Block %d\n", bt->index);
//		i++;
		dvg_list.push_back(((block_information *) (bt->aux))->get_points_out());
	}
//	fprintf(dump_file,"\nNumber of Predecessors %d\n",i);

	if (dvg_list.size() == 1) {
//		fprintf(dump_file,"\nNo call to meet\n");
		return dvg_list[0];
	}

	g = dvg_list[0].meet(bb, dvg_list[1], cnode, false);

//	fprintf(dump_file,"\nMeet of G1 and G2 is \n");
//	fprintf(dump_file,"\nG1\n");
//	dvg_list[0].print_graph();
//	fprintf(dump_file,"\nG2\n");
//	dvg_list[1].print_graph();
//	fprintf(dump_file,"\nMeet G\n");
//	g.print_graph();

	for (i = 2; i < dvg_list.size(); i++) {
//		fprintf(dump_file,"\nMore than 2 predecessors\n");
		g = g.meet(bb, dvg_list[i], cnode, false);
	}

	return g;
}

void get_local_info(basic_block bb, struct cgraph_node *cnode) {
	edge e;
	edge_iterator ei;

	map<edge_id, unsigned int> temp_map, local_map;
	map<edge_id, unsigned int>::iterator mit;

	if (((block_information *) (bb->aux))->start_block) {
		return;
	}

	FOR_EACH_EDGE(e,ei,bb->preds)
	{
		basic_block bt = e->src;

		temp_map = ((block_information *) (bt->aux))->order_out;

		for (mit = temp_map.begin(); mit != temp_map.end(); mit++) {
			if (local_map[mit->first] < mit->second) {
				local_map[mit->first] = mit->second;
			}
		}
	}

	((block_information *) (bb->aux))->order_in = local_map;
	((block_information *) (bb->aux))->order_out = local_map;
}

live_info get_out_live_info(basic_block bb, struct cgraph_node *cnode) {
	edge e;
	edge_iterator ei;
	int i;

	live_info result, temp;

	if (((block_information *) (bb->aux))->end_block) {
//		fprintf(dump_file,"\nStart Block %d Function %s", bb->index, cgraph_node_name(cnode));
		return ((block_information *) (bb->aux))->get_live_out();
	}

	FOR_EACH_EDGE(e,ei,bb->succs)
	{
//		fprintf(dump_file,"\nBasic Block %d\n", bb->index);
		basic_block bt = e->dest;
//		fprintf(dump_file,"\nSuccessor Basic Block %d\n", bt->index);
//		i++;
		temp = ((block_information *) (bt->aux))->get_live_in();

		result = result.meet_live(temp, cnode);
	}
//	fprintf(dump_file,"\nNumber of Successors %d\n",i);

	return result;
}

void get_succ_basic_block(basic_block bb, cgraph_node *c) {
	edge e;
	edge_iterator ei;

	if (((block_information *) (bb->aux))->end_block)
		return;

#if 1
	FOR_EACH_EDGE(e,ei,bb->succs)
	{
		if (e->dest == NULL)
			continue;

		basic_block bt = e->dest;
//		fprintf(dump_file,"\n%s Succ %d -> %d\n", cgraph_node_name(c), bb->index, bt->index);

//                if(!((function_info *)(c->aux))->is_present(bt,2))
//                        ((function_info *)(c->aux))->push_back(bt,2);

		((function_info *) (c->aux))->points_worklist[((function_info *) (c->aux))->bb_rp_order[bt->index]] = true;
	}
#endif

#if 0
	unsigned int nbb = ((function_info *)(c->aux))->get_num_bb();

	for(int i = 0; i < nbb; i++)
	{
		((function_info *)(c->aux))->points_worklist[i] = true;
	}
#endif
}

void get_pred_basic_block(basic_block bb, cgraph_node *c) {
	edge e;
	edge_iterator ei;

	if (((block_information *) (bb->aux))->start_block)
		return;

#if 1
	FOR_EACH_EDGE(e,ei,bb->preds)
	{
		if (e->src == NULL)
			continue;

		basic_block bt = e->src;

//                if(!((function_info *)(c->aux))->is_present(bt,1))
//                        ((function_info *)(c->aux))->push_back(bt,1);

		((function_info *) (c->aux))->live_worklist[((function_info *) (c->aux))->bb_p_order[bt->index]] = true;
//		fprintf(dump_file,"\nPred Basic Block Index %d\n", bt->index);
//		fprintf(dump_file,"\nPred Order %d\n", ((function_info *)(c->aux))->bb_p_order[bt->index]);
	}
#endif

#if 0
	unsigned int nbb = ((function_info *)(c->aux))->get_num_bb();

	for(int i = 0; i < nbb; i++)
	{
		((function_info *)(c->aux))->live_worklist[i] = true;
	}
#endif

}

void process_intra_block_live(basic_block bb, struct cgraph_node *cnode) {
	rit ai;

	live_info l_out_prev = ((block_information *) (bb->aux))->get_live_out();

	DVG pin = ((block_information *) (bb->aux))->get_points_in();

	live_info l_out_new = get_out_live_info(bb, cnode);

	live_info l_out = l_out_prev.meet_live(l_out_new, cnode);

	((block_information *) (bb->aux))->set_live_out(l_out);

	fprintf(dump_file, "\nLive OUT\n");
	l_out.print_live_info();

//	fprintf(dump_file,"\nAfter Printing Live OUT\n");

	live_info l_in, l_in_prev, l_in_new, l_temp;

	l_in_prev = ((block_information *) (bb->aux))->get_live_in();
	l_in_new = l_out.copy_live_info();

	constraint_list con = ((block_information *) (bb->aux))->get_list();

	for (ai = con.rbegin(); ai != con.rend(); ai++) {

		if (!(*ai).get_bool()) {
			live_type temp_live = l_in_new.get_l_info();
			temp_live.insert((*ai).get_int());

			l_in_new.set_l_info(temp_live);

//			fprintf(dump_file,"\nUnconditional Liveness Generation\n");
//			l_in_new.print_live_info();

			continue;
		}

		constraint_t cons = VEC_index(constraint_t, aliases, (*ai).get_int());

//		fprintf(dump_file,"\nConstraint LHS %d %s; RHS %d %s\n",cons->lhs.var,VEC_index(csvarinfo_t, csvarmap, cons->lhs.var)->name,cons->rhs.var,VEC_index(csvarinfo_t, csvarmap, cons->rhs.var)->name);	

//		if(cons->rhs.ptr_arith == true)
//			fprintf(dump_file,"\nPointer Arithmetic\n");

//		fprintf(dump_file,"\nLIN\n");
//		l_in_new.print_live_info();

		l_temp = l_in_new;

		l_in_new.generate_live_info(cons, cnode, (*ai).get_int(), l_temp, pin);
//		fprintf(dump_file,"\nAdding Constraint...\n");
//		g_out.print_dvg();

//		(*ai).set_order();	

	}

	if (((block_information *) (bb->aux))->linitialized == 1) {
//		fprintf(dump_file,"\nGet succs\n");
//		g_out = g_out_new; 
		l_in = l_in_new; // l_in_prev.meet_live(l_in_new, cnode);

		((block_information *) (bb->aux))->set_live_in(l_in);
		get_pred_basic_block(bb, cnode);
		((block_information *) (bb->aux))->linitialized = 0;
		fprintf(dump_file, "\nLive IN\n");
//		fprintf(dump_file, "\n\nFunction %s Other Block No %d ", cgraph_node_name(cnode), bb->index);
		l_in.print_live_info();
	} else {
//		g_out = g_out_new; 
		l_in = l_in_prev.meet_live(l_in_new, cnode);

		if (!(l_in_prev == l_in)) {
//			fprintf(dump_file,"\nDVG OUT Changed\n");
//			fprintf(dump_file,"\nPrev DVG OUT\n");
//			g_out_prev.print_dvg();
//			fprintf(dump_file,"\nNew DVG OUT\n");
//			g_out.print_dvg();

			((block_information *) (bb->aux))->set_live_in(l_in);
			get_pred_basic_block(bb, cnode);
			fprintf(dump_file, "\nLive IN\n");
//			fprintf(dump_file, "\n\nFunction %s Other Block No %d ", cgraph_node_name(cnode), bb->index);
			l_in.print_live_info();
		}
	}
}

void process_intra_block(basic_block bb, struct cgraph_node *cnode) {
	it ai;

	DVG g_in_prev = ((block_information *) (bb->aux))->get_points_in();

	DVG g_in_new = get_in_points_to_info(bb, cnode);

//	DVG g_in = g_in_prev.meet(bb, g_in_new, cnode, false);
	DVG g_in = g_in_new;

	((block_information *) (bb->aux))->set_points_in(g_in);

	fprintf(dump_file, "\nDVG IN\n");
	g_in.print_dvg();

//	fprintf(dump_file,"\nAfter Printing DVG IN\n");

	DVG g_out, g_out_prev, g_out_new, g_out1;

	g_out_prev = ((block_information *) (bb->aux))->get_points_out();
	g_out_new = g_in.copy_dvg();

	live_info l_out = ((block_information *) (bb->aux))->get_live_out();

	live_type temp_live = l_out.get_l_info();

	DVG out;

	constraint_list con = ((block_information *) (bb->aux))->get_list();

	for (ai = con.begin(); ai != con.end(); ai++) {

		if (!(*ai).get_bool())
			continue;

		constraint_t cons = VEC_index(constraint_t, aliases, (*ai).get_int());

//		fprintf(dump_file,"\nConstraint LHS %d %s; RHS %d %s\n",cons->lhs.var,VEC_index(csvarinfo_t, csvarmap, cons->lhs.var)->name,cons->rhs.var,VEC_index(csvarinfo_t, csvarmap, cons->rhs.var)->name);	

//		if(cons->rhs.ptr_arith == true)
//			fprintf(dump_file,"\nPointer Arithmetic\n");

		g_out_new.generate_graph(bb, cons, cnode, (*ai).get_int());
//		fprintf(dump_file,"\nAdding Constraint...\n");
//		g_out.print_dvg();

//		(*ai).set_order();	

	}

#if LIVENESS
	set_edges elist, remove;

	elist = g_out_new.get_edge_list();

	edge_it eit;
	Edge e;
	Node lhs;
	unsigned int lhs_var;

	set<unsigned int> pars = ((function_info *)(cnode->aux))->get_params();
	unsigned int ret_id = ((function_info *)(cnode->aux))->get_ret_id();

	for(eit = elist.begin(); eit != elist.end(); eit++)
	{
		e = get_edge(*eit);
		lhs = e.get_lhs();
		lhs_var = lhs.get_var_id();

		if(CDV.find(lhs.get_var_id()) == CDV.end())
		{
//			if((!global_var(lhs_var))) // || (lhs_var != ret_id) || (pars.find(lhs_var) == pars.end()))
//			{
//				remove.insert(*eit);
//			}
			if((!global_var(lhs_var)) && (temp_live.find(lhs_var) == temp_live.end()) && (lhs_var != ret_id) && (pars.find(lhs_var) == pars.end()))
			{
//				fprintf(dump_file,"\nEdge Removed due to Liveness\n");
//				e.print_edge();
				remove.insert(*eit);
			}
		}
	}

	g_out_new.remove_edges(bb, remove, cnode, false);
#endif

	if (((block_information *) (bb->aux))->pinitialized == 1) {
//		fprintf(dump_file,"\nGet succs\n");
		g_out = g_out_new;
//		g_out = g_out_prev.meet(bb, g_out_new, cnode, false);

		((block_information *) (bb->aux))->set_points_out(g_out);
		get_succ_basic_block(bb, cnode);
		((block_information *) (bb->aux))->pinitialized = 0;
		fprintf(dump_file, "\nDVG OUT\n");
		fprintf(dump_file, "\n\nPFunction %s Other Block No %d ", cgraph_node_name(cnode), bb->index);
		g_out.print_dvg();

#if 1
//		if(((function_info *)(cnode->aux))->count > 3)   // Function composition with no kill if function is being processed more than twice
		{
			if (end_bb_of_fn(cnode)->index == bb->index) // This is the Exit Block
			{
				struct cgraph_edge *edge;
				struct cgraph_node *node;
				struct function *fn;
				basic_block call_block;

				list<struct cgraph_node *> temp_func;
				list<struct cgraph_node *>::iterator tfit;

				for (edge = cnode->callers; edge; edge = edge->next_caller) {
					node = edge->caller;

					if (!gimple_has_body_p(node->decl) || node->clone_of)
						continue;

					if (find(temp_func.begin(), temp_func.end(), node) == temp_func.end()) {
						temp_func.push_back(node);
					}
				}

				for (tfit = temp_func.begin(); tfit != temp_func.end(); tfit++) {
					node = *tfit;

//				if(find(func_worklist.begin(), func_worklist.end(), node) == func_worklist.end())
					{
//					func_worklist.push_back(node);
//					func_worklist.push_front(node);

//					if(!function_worklist[func_index_array[((function_info *)(node->aux))->func_num]])
//						fprintf(dump_file,"\nPush Caller on Worklist %s due to Processing Function %s Order in the Worklist \n",cgraph_node_name(node), cgraph_node_name(cnode), func_index_array[((function_info *)(node->aux))->func_num]);

						function_worklist[func_index_array[((function_info *) (node->aux))->func_num]] = true;

//					fprintf(dump_file,"\nFunction Pushed onto the Worklist %s\n", cgraph_node_name(node));

						if (((function_info *) (node->aux))->is_visited()) {
							fn = DECL_STRUCT_FUNCTION(node->decl);

							node_it nit;

							set<unsigned int> call_list = ((function_info *) (node->aux))->call_block_list;

							for (nit = call_list.begin(); nit != call_list.end(); nit++) {
								call_block = BASIC_BLOCK_FOR_FUNCTION(fn, *nit);
								((function_info *) (node->aux))->points_worklist[((function_info *) (node->aux))->bb_rp_order[*nit]] = true;
							}
						} else {
							unsigned int nbb = ((function_info *) (node->aux))->get_num_bb();

							for (int i = 0; i < nbb; i++) {
								((function_info *) (node->aux))->points_worklist[i] = true;
							}
						}
					}
				}

				func_worklist.sort();
			}
		}
#endif
	} else {
		g_out = g_out_new;
//		g_out = g_out_prev.meet(bb, g_out_new, cnode, false);

#if STATS
		gcomp_count++;

//		fprintf(dump_file,"\nGraph Comparison Count so far %d\n", gcomp_count);
#endif

		if (!(g_out_prev == g_out)) {
//			fprintf(dump_file,"\nDVG OUT Changed\n");
//			fprintf(dump_file,"\nPrev DVG OUT\n");
//			g_out_prev.print_dvg();
//			fprintf(dump_file,"\nNew DVG OUT\n");
//			g_out.print_dvg();

#if INCFCOMP
			((function_info *)(cnode->aux))->set_prev_dvg(g_out_prev);
//			fprintf(dump_file,"\nSaved Previous DVG in Function %s\n", cgraph_node_name(cnode));
//			g_out_prev.print_dvg();			
#endif

			((block_information *) (bb->aux))->set_points_out(g_out);
			get_succ_basic_block(bb, cnode);
			fprintf(dump_file, "\nDVG OUT\n");
			fprintf(dump_file, "\n\nPFunction %s Other Block No %d ", cgraph_node_name(cnode), bb->index);
			g_out.print_dvg();

			if (!g_out.weaker(g_out_prev, cnode)) {
				fprintf(dump_file, "\nNot a Valid Operation - Non-Monotone\n");

//				fprintf(dump_file,"\ng_out\n");
//				g_out.print_dvg();

//				fprintf(dump_file,"\ng_out_prev\n");
//				g_out_prev.print_dvg();
			}

#if 1
//			if(((function_info *)(cnode->aux))->count > 3)   // Function composition with no kill if function is being processed more than twice
			{
				if (end_bb_of_fn(cnode)->index == bb->index) // This is the Exit Block
				{
					struct cgraph_edge *edge;
					struct cgraph_node *node;
					struct function *fn;
					basic_block call_block;

					list<struct cgraph_node *> temp_func;
					list<struct cgraph_node *>::iterator tfit;

					for (edge = cnode->callers; edge; edge = edge->next_caller) {
						node = edge->caller;

						if (!gimple_has_body_p(node->decl) || node->clone_of)
							continue;

						if (find(temp_func.begin(), temp_func.end(), node) == temp_func.end()) {
							temp_func.push_back(node);
						}
					}

					for (tfit = temp_func.begin(); tfit != temp_func.end(); tfit++) {
						node = *tfit;

//					if(find(func_worklist.begin(), func_worklist.end(), node) == func_worklist.end())
						{
//						func_worklist.push_back(node);
//						func_worklist.push_front(node);

//						function_worklist[func_index_array[node->uid]] = true;

//						if(!function_worklist[func_index_array[((function_info *)(node->aux))->func_num]])
//							fprintf(dump_file,"\nPush Caller on Worklist %s due to Processing Function %s Order in the Worklist \n",cgraph_node_name(node), cgraph_node_name(cnode), func_index_array[((function_info *)(node->aux))->func_num]);

							function_worklist[func_index_array[((function_info *) (node->aux))->func_num]] = true;

//						fprintf(dump_file,"\nIndex %d\n", func_index_array[((function_info *)(node->aux))->func_num]);

//						fprintf(dump_file,"\nKasa Kay\n");

							if (((function_info *) (node->aux))->is_visited()) {
								fn = DECL_STRUCT_FUNCTION(node->decl);

								node_it nit;

								set<unsigned int> call_list = ((function_info *) (node->aux))->call_block_list;

								for (nit = call_list.begin(); nit != call_list.end(); nit++) {
									call_block = BASIC_BLOCK_FOR_FUNCTION(fn, *nit);
									((function_info *) (node->aux))->points_worklist[((function_info *) (node->aux))->bb_rp_order[*nit]] = true;
								}
							} else {
								unsigned int nbb = ((function_info *) (node->aux))->get_num_bb();

								for (int i = 0; i < nbb; i++) {
									((function_info *) (node->aux))->points_worklist[i] = true;
								}
							}
						}
					}
//				func_worklist.sort();
				}
			}
#endif

		}
	}
}

void process_call_block_live(basic_block bb, struct cgraph_node *cnode) {
//	fprintf(dump_file,"\nInside Call Block\n");

	live_info l_out = get_out_live_info(bb, cnode);
	fprintf(dump_file, "\nLive OUT\n");
	l_out.print_live_info();

	live_info l_in, l_in_prev;

	l_in_prev = ((block_information *) (bb->aux))->get_live_in();
	l_in = l_out.copy_live_info();

	if (((block_information *) (bb->aux))->linitialized == 1) {
		((block_information *) (bb->aux))->set_live_in(l_in);
		get_pred_basic_block(bb, cnode);
		((block_information *) (bb->aux))->linitialized = 0;
		fprintf(dump_file, "\nLive IN\n");
		l_in.print_live_info();
	} else {
		if (!(l_in_prev == l_in)) {
			((block_information *) (bb->aux))->set_live_in(l_in);
			get_pred_basic_block(bb, cnode);
			fprintf(dump_file, "\nLive IN\n");
			l_in.print_live_info();
		}
	}
}

void push_caller_for_scc(struct cgraph_node *cnode) {
	struct cgraph_edge *edge;

	struct cgraph_node *node;

	node = NULL;

//	fprintf(dump_file,"\nHiiii\n");

//	fprintf(dump_file,"\nCnode %s\n", cgraph_node_name(cnode));
//	fprintf(dump_file,"\nGCnode %s\n", cgraph_node_name(gcnode));

	for (edge = cnode->callers; edge; edge = edge->next_caller) {
		node = edge->caller;

//		fprintf(dump_file,"\nCaller node %s\n", cgraph_node_name(node));

		if (node) {
			if (node->order != gcnode->order) {

				if (find(cnodes_list_callers.begin(), cnodes_list_callers.end(), node) == cnodes_list_callers.end()) {
					cnodes_list_callers.push_front(node);

					push_caller_for_scc(node);
				}
			}
		}
	}
}

DVG get_out_exit_block(struct cgraph_node *cnode) {
//	set< unsigned int > pred_temp = end_bb_of_fn(cnode);

	set<unsigned int>::iterator it;

	struct function *fn;
	basic_block bt;

	fn = DECL_STRUCT_FUNCTION(cnode->decl);

	DVG g;
	set<DVG> dvg_set;
	set<DVG>::iterator temp;
	basic_block bb;

#if 0
	for(it = pred_temp.begin(); it != pred_temp.end(); it++)
	{
		bb = BASIC_BLOCK_FOR_FUNCTION(fn, *it);
		g = ((block_information *)(bb->aux))->get_points_out();

		dvg_set.insert(g);
	}

	if(dvg_set.size())
	{
		temp = dvg_set.begin();

		return temp;
	}
	else if (dvg_set.empty())
	{
		return g;
	}
	else
	{
		for(temp = dvg_set.begin(); temp != dvg_set.end(); temp++)
		{
			g = g.meet(bt, *temp, cnode, false);
		}

		return g;
	}
#endif

	return g;
}

void process_call_block(basic_block bb, struct cgraph_node *cnode) {
//	fprintf(dump_file,"\nInside Call Block\n");

	it ai;
	DVG g_in_prev = ((block_information *) (bb->aux))->get_points_in();

	DVG g_in_new = get_in_points_to_info(bb, cnode);

	DVG g_in = g_in_new; // .meet(bb, g_in_new, cnode, false);
//	DVG g_in = g_in_prev.meet(bb, g_in_new, cnode, false);

	((block_information *) (bb->aux))->set_points_in(g_in);

	fprintf(dump_file, "\nDVG IN\n");
	g_in.print_dvg();

//	fprintf(dump_file,"\nhiiiiiii\n");

	DVG g_out, g_out_prev, g_out_new;

	g_out_prev = ((block_information *) (bb->aux))->get_points_out();
	g_out_new = g_in.copy_dvg();
//        g_out = g_in.copy_dvg();

	live_info l_out = ((block_information *) (bb->aux))->get_live_out();

	live_type temp_live = l_out.get_l_info();

//	struct cgraph_node *node;

	constraint_list con = ((block_information *) (bb->aux))->get_list();
	unsigned last_edge_con_id;

	for (ai = con.begin(); ai != con.end(); ai++) {
		if (!(*ai).get_bool())
			continue;

		constraint_t cons = VEC_index(constraint_t, aliases, (*ai).get_int());

//		fprintf(dump_file,"\nConstraint LHS %d %s; RHS %d %s\n",cons->lhs.var,VEC_index(csvarinfo_t, csvarmap, cons->lhs.var)->name,cons->rhs.var,VEC_index(csvarinfo_t, csvarmap, cons->rhs.var)->name);	

		g_out_new.generate_graph(bb, cons, cnode, (*ai).get_int());
	}

	gimple stmt = bb_call_stmt(bb);

	tree decl = get_called_fn_decl(stmt);
	struct cgraph_node *node;
	DVG callee_dvg;
	struct function *called_function;
	basic_block endbb;

	struct cgraph_edge *edge;
	struct cgraph_node *temp_node;
	set_cnodes temp;

	set_cnodes::iterator cnode_it;
	DVG ftop, prev_dvg;

	node = NULL;
	bool to_kill = true;

	if (TREE_CODE (decl) == FUNCTION_DECL) {
		called_function = DECL_STRUCT_FUNCTION(decl);

		node = cgraph_get_node(decl);

		endbb = end_bb_of_fn(node);

#if STATS
		((function_info *)(node->aux))->use_count++;

//		fprintf(dump_file,"\nSummary Flow Function of %s used  %d number of times\n", cgraph_node_name(node), ((function_info *)(node->aux))->use_count); 
#endif

		if (((function_info *) (node->aux))->count != 0) {
			to_kill = false;
//		fprintf(dump_file,"\nCall Block Callee %s\n",cgraph_node_name(node));

			callee_dvg = ((block_information *) (endbb->aux))->get_points_out();

			set_edges temp_edges1 = callee_dvg.get_edge_list();
			set_edges temp_edges2, temp_edges;

#if INCFCOMP
			prev_dvg = ((function_info *)(node->aux))->get_prev_dvg();
			temp_edges2 = prev_dvg.get_edge_list();

			set_difference(temp_edges1.begin(), temp_edges1.end(), temp_edges2.begin(), temp_edges2.end(), inserter(temp_edges, temp_edges.end()));
//		fprintf(dump_file,"\nIn incre func comp f0\n");
//		print_set_edges(temp_edges1);
//		fprintf(dump_file,"\nIn incre func comp f1\n");
//		print_set_edges(temp_edges2);
//		fprintf(dump_file,"\nIn incre func comp diff dvg\n");
//		print_set_edges(temp_edges);
#endif

#if FCOMP
			temp_edges = temp_edges1;
#endif

			set_edges f_edges, diff_edges;
			set_edges::iterator tit;

			set<unsigned int> pars = ((function_info *) (node->aux))->get_params();
			unsigned int ret_id = ((function_info *) (node->aux))->get_ret_id();

			map<unsigned int, set_edges> map_flow_sens, temp_map;

			map<edge_id, unsigned int> rev_temp_map;

			temp_map = ((function_info *) (node->aux))->get_order_map();
			rev_temp_map = ((function_info *) (node->aux))->get_rev_order_map();

			map<unsigned int, set_edges>::iterator mit;

			unsigned int order_id;
			Edge e1;

			for (tit = temp_edges.begin(); tit != temp_edges.end(); tit++) {
				e1 = get_edge(*tit);
//			fprintf(dump_file,"\nEdge for Function Composition\n");
//			e1.print_edge();

				order_id = rev_temp_map[*tit];

//			fprintf(dump_file,"\nOrder of Edge %d\n", order_id);

				f_edges = map_flow_sens[order_id];

				f_edges.insert(*tit);

				map_flow_sens[order_id] = f_edges;
			}

			edge_it eit;
			unsigned int con_id;
			Edge e;
			Node lhs, rhs;
			unsigned int var, lhs_var;

			for (mit = map_flow_sens.begin(); mit != map_flow_sens.end(); mit++) {
				f_edges = mit->second;
				con_id = mit->first;

				for (eit = f_edges.begin(); eit != f_edges.end(); eit++) {
					e = get_edge(*eit);

					if (e.is_boundary_edge()) {
//					fprintf(dump_file,"\nBoundary Edge\n");
						continue;
					}

//				fprintf(dump_file,"\nEdge from Callee DVG\n");
					e.print_edge();

//				fprintf(dump_file,"\nHiii\n");

					lhs_var = e.get_lhs().get_var_id();

					if ((!global_var(lhs_var)) && (lhs_var != ret_id) && (pars.find(lhs_var) == pars.end()) && (CDV.find(lhs_var) == CDV.end())) {
						continue;
					}

					lhs = e.get_lhs();
					rhs = e.get_rhs();

					var = lhs.get_var_id();

					if (CDV.find(var) != CDV.end()) {

						lhs.set_var_id(var - 1);
						lhs.add_node_map();
					}

					var = rhs.get_var_id();

					if (CDV.find(var) != CDV.end()) {

						rhs.set_var_id(var - 1);
						rhs.add_node_map();
					}

#if 0
					if(lhs == rhs || e.is_self_loop())
					{
						continue;
					}
#endif

					Edge e_temp(lhs, rhs);

#if INCFCOMP
					g_out_new.func_comp(bb, e_temp, cnode, con_id, callee_dvg, node, false);
#endif

#if FCOMP
					g_out_new.func_comp(bb, e_temp, cnode, con_id, callee_dvg, node, false);
#endif
				}
			}

			// On Fly Constraint Construction for Return Type

			if (((function_info *) (node->aux))->has_ret_type()) {
//			((function_info *)(cnode->aux))->cons_num++;

//			fprintf(dump_file,"\nReturn Type for Call\n");

				unsigned int ret_id = ((function_info *) (node->aux))->get_ret_id();

//			fprintf(dump_file,"\nRet ID %d\n", ret_id);

				tree lhsop = gimple_call_lhs(stmt);

				csvarinfo_t vi = NULL;

				if (lhsop) {
//			fprintf(dump_file,"\nRet Var %s\n", get_name(lhsop));

//			csvarinfo_t vi = cs_lookup_vi_for_tree(lhsop);
					vi = cs_get_vi_for_tree(lhsop, bb, cnode);
				}

//			fprintf(dump_file,"\nHiiii\n");

				il il1;
				il1.add_deref(NDEREF);

				if (lhsop && vi != NULL) {
//				fprintf(dump_file,"\nNew Edge Generated For Return Type\n");
					rhs.set_var_id(ret_id);
					rhs.set_ind_list(il1);
					rhs.add_node_map();

					rhs.print_node();

					lhs.set_var_id(vi->id);
					lhs.set_ind_list(il1);
					lhs.add_node_map();

					Edge e_temp(lhs, rhs);

					g_out_new.func_comp(bb, e_temp, cnode, con_id, callee_dvg, node, false);
				}

			}
		}

//		fprintf(dump_file,"\nAfter Function Composition\n");
//		g_out_new.print_dvg();
	}
#if 1
	else {
		func_ptr_count++;
		// Function Pointer	
	}
#endif

	if (to_kill) {
		g_out_new = ftop.copy_dvg();
	}

#if LIVENESS
	set_edges elist, remove;

	elist = g_out_new.get_edge_list();

	edge_it eit;
	Edge e;
	Node lhs;
	unsigned int lhs_var;

	set<unsigned int> pars = ((function_info *)(cnode->aux))->get_params();
	unsigned int ret_id = ((function_info *)(cnode->aux))->get_ret_id();

	for(eit = elist.begin(); eit != elist.end(); eit++)
	{
		e = get_edge(*eit);
		lhs = e.get_lhs();
		lhs_var = lhs.get_var_id();

		if(CDV.find(lhs.get_var_id()) == CDV.end())
		{
//			if(temp_live.find(lhs_var) == temp_live.end())
//			{
//				remove.insert(*eit);
//			}
//			else if((!global_var(lhs_var))) // || (lhs_var != ret_id) || (pars.find(lhs_var) == pars.end()))
			if((!global_var(lhs_var)) && (temp_live.find(lhs_var) == temp_live.end()) && (lhs_var != ret_id) && (pars.find(lhs_var) == pars.end()))
			{
				remove.insert(*eit);
			}
		}
	}

	g_out_new.remove_edges(bb, remove, cnode, false);
#endif

	func_it fit;
	struct function *fn;
	basic_block call_block;

//	g_out = g_out_new;
#if INCFCOMP
	g_out = g_out_prev.meet(bb, g_out_new, cnode, false);
//	g_out = prev_dvg.meet(bb, g_out_new, cnode, false);
#endif

#if FCOMP
	g_out = g_out_new.copy_dvg();
#endif

	if (((block_information *) (bb->aux))->pinitialized == 1) {
//		fprintf(dump_file,"\nGet succs\n");
//		g_out = g_out_new; // .meet(bb, g_out_new, cnode, false);
//		g_out = g_out_prev.meet(bb, g_out_new, cnode, false);

		((block_information *) (bb->aux))->set_points_out(g_out);
		get_succ_basic_block(bb, cnode);
		((block_information *) (bb->aux))->pinitialized = 0;
		fprintf(dump_file, "\nDVG OUT\n");
		fprintf(dump_file, "\nPFunction %s Other Block No %d ", cgraph_node_name(cnode), bb->index);
		g_out.print_dvg();

	} else {
//		g_out = g_out_new; 
//		g_out = g_out_prev.meet(bb, g_out_new, cnode, false);

//		fprintf(dump_file,"\nKasa Kay %d\n",((block_information *)(bb->aux))->pinitialized);

		if (!(g_out_prev == g_out)) {
//			fprintf(dump_file,"\nDVG OUT Changed\n");
//			fprintf(dump_file,"\nPrev DVG OUT\n");
//			g_out_prev.print_dvg();
//			fprintf(dump_file,"\nNew DVG OUT\n");
//			g_out.print_dvg();

			if (!g_out.weaker(g_out_prev, cnode)) {
				fprintf(dump_file, "\nNot a Valid Operation - Non-Monotone\n");

//				fprintf(dump_file,"\ng_out\n");
//				g_out.print_dvg();

//				fprintf(dump_file,"\ng_out_prev\n");
//				g_out_prev.print_dvg();
			}

			((block_information *) (bb->aux))->set_points_out(g_out);
			get_succ_basic_block(bb, cnode);
			fprintf(dump_file, "\nDVG OUT\n");
			fprintf(dump_file, "\nPFunction %s Other Block No %d ", cgraph_node_name(cnode), bb->index);
			g_out.print_dvg();

		}
	}
}

void do_liveness(struct cgraph_node *cnode) {
	fprintf(dump_file, "\n=========================Liveness Pass %s ==============================\n", cgraph_node_name(cnode));

	struct function *fn;

	fn = DECL_STRUCT_FUNCTION(cnode->decl);

	int i;
	unsigned int nbb = ((function_info *) (cnode->aux))->get_num_bb();

	basic_block bb;

	while (!(((function_info *) (cnode->aux))->is_empty_worklist(1))) {
		for (i = 0; i < nbb; i++) {
			if (((function_info *) (cnode->aux))->live_worklist[i]) {
				bb = BASIC_BLOCK_FOR_FUNCTION(fn, ((function_info * )(cnode->aux))->post_order[i]);

				if (((block_information *) (bb->aux))->call_block) {
					fprintf(dump_file, "\nFunction %s Call Block No %d\n", cgraph_node_name(cnode), bb->index);
					process_call_block_live(bb, cnode);
					((function_info *) (cnode->aux))->live_worklist[i] = false;
				} else {
					fprintf(dump_file, "\n\nFunction %s Other Block No %d ", cgraph_node_name(cnode), bb->index);
					process_intra_block_live(bb, cnode);
					((function_info *) (cnode->aux))->live_worklist[i] = false;

//					fprintf(dump_file, "\n\nFunction %s Other Block No %d ", cgraph_node_name(cnode), bb->index);
//					((block_information *)(bb->aux))->get_points_out().print_dvg();
				}

			}
		}
	}
}

void do_points_to(struct cgraph_node *cnode) {
	fprintf(dump_file, "\n=========================Points-to Pass %s  Order %d ==============================\n", cgraph_node_name(cnode), cnode->uid);

	struct function *fn;

	fn = DECL_STRUCT_FUNCTION(cnode->decl);

	int i;
	unsigned int nbb = ((function_info *) (cnode->aux))->get_num_bb();

	basic_block bb;

	while (!(((function_info *) (cnode->aux))->is_empty_worklist(2))) {
		for (i = 0; i < nbb; i++) {
			if (((function_info *) (cnode->aux))->points_worklist[i]) {
				bb = BASIC_BLOCK_FOR_FUNCTION(fn, ((function_info * )(cnode->aux))->rev_post_order[i]);

				if (((block_information *) (bb->aux))->call_block) {
					fprintf(dump_file, "\nFunction %s Call Block No %d\n", cgraph_node_name(cnode), bb->index);
					process_call_block(bb, cnode);
					((function_info *) (cnode->aux))->points_worklist[i] = false;
				} else {
//					fprintf(dump_file, "\n\nFunction %s Other Block No %d ", cgraph_node_name(cnode), bb->index);
					process_intra_block(bb, cnode);
					((function_info *) (cnode->aux))->points_worklist[i] = false;

//					fprintf(dump_file, "\n\nFunction %s Other Block No %d ", cgraph_node_name(cnode), bb->index);
//					((block_information *)(bb->aux))->get_points_out().print_dvg();
				}

			}
		}
	}

}

void update_boundary_info() {
	struct cgraph_node *cnode;
	node_it nit;

	set_edges temp, bound_edges;
	live_type result;
	basic_block startbb;
	set<struct cgraph_node *> set_callers;
	set<struct cgraph_node *>::iterator it;

	for (cnode = cgraph_nodes; cnode; cnode = cnode->next) {
		if (!gimple_has_body_p(cnode->decl) || cnode->clone_of)
			continue;

#if 0
		if (strcmp (IDENTIFIER_POINTER (DECL_NAME (cnode->decl)), "main") == 0)
		{
			continue;
		}
#endif

		set_callers.insert(cnode);
	}

	for (it = set_callers.begin(); it != set_callers.end(); it++) {
		cnode = *it;

//		fprintf(dump_file,"\nFunction %s\n",cgraph_node_name(cnode));

		startbb = start_bb_of_fn(cnode);

		result = ((block_information *) (startbb->aux))->get_live_in().get_l_info();

//		fprintf(dump_file,"\nKay Chalu\n");
		for (nit = result.begin(); nit != result.end(); nit++) {
			if (global_var(*nit)) {
				temp = create_boundary_edges(*nit);

				bound_edges.insert(temp.begin(), temp.end());
			}
		}

//		fprintf(dump_file,"\nIn Function %s\n", cgraph_node_name(cnode));
//		fprintf(dump_file,"\nBound Edges to Be Pushed to the Caller\n");
//		print_set_edges(bound_edges);

		push_bound_info_callers(cnode, bound_edges);

//		fprintf(dump_file,"\nHelloooooo\n");	
	}
//	fprintf(dump_file,"\nItheee\n");
}

void perform_analysis(struct cgraph_node *cnode) {
	iter = 1;

#if STATS
	starttime();
#endif

#if LIVENESS
	while(!((function_info *)(cnode->aux))->is_empty_worklist(1))
	{
		do_liveness(cnode);
	}
#endif

#if STATS && LIVENESS
	ttime = stoptime();

	liveness_time_s += ttime;

//	fprintf(dump_file,"\nLiveness Pass for Function %s, Overall Time Taken: %lg, Time Taken for this Pass %lg\n", cgraph_node_name(cnode), liveness_time_s, ttime);
#endif

	if (iter == 1) {
#if LIVENESS != 1
		do_liveness(cnode);
		update_boundary_info();
#endif

#if LIVENESS
		update_boundary_info();
#endif
	}

//	fprintf(dump_file,"\nBegin Points-to Pass\n");

#if STATS
	starttime();
#endif

#if LIVENESS
	while(!((function_info *)(cnode->aux))->is_empty_worklist(2))
	{
#endif
	do_points_to(cnode);
#if LIVENESS
}
#endif

#if STATS
	ttime = stoptime();

	points_to_time_s += ttime;

//	fprintf(dump_file,"\nPoints-to Pass for Function %s, Overall Time Taken: %lg, Time Taken for this Pass %lg\n", cgraph_node_name(cnode), points_to_time_s, ttime);
#endif

	((function_info *) (cnode->aux))->set_visited(true);

	iter++;

//	double temp_p = stoptime();
//	points_to_time += temp_p;

//	iter++;
}

void get_size_of_summary_flow_function(struct cgraph_node *cnode) {
	fprintf(dump_file, "\nStatistics of DVG of %s\n", cgraph_node_name(cnode));

	unsigned int con_dep_edge = 0, con_ind_edge = 0, deref_edge = 0, dvg_size = 0, total_dvg_size = 0;
	basic_block endbb = end_bb_of_fn(cnode);

	DVG callee_dvg = ((block_information *) (endbb->aux))->get_points_out();

	set_edges temp_edges = callee_dvg.get_edge_list();
	set_edges f_edges, diff_edges;
	il il1;

	edge_it eit;
	unsigned int con_id;
	Edge e;
	Node lhs, rhs;
	unsigned int rhs_var, lhs_var;

	set_edges::iterator it;

	set<unsigned int> pars = ((function_info *) (cnode->aux))->get_params();
	unsigned int ret_id = ((function_info *) (cnode->aux))->get_ret_id();

	set<node_id> temp_nodes;

	for (it = temp_edges.begin(); it != temp_edges.end(); it++) {
		e = get_edge(*it);

		if (e.is_boundary_edge()) {
//			fprintf(dump_file,"\nBoundary Edge\n");
			continue;
		}

		total_dvg_size++;

		lhs = e.get_lhs();
		rhs = e.get_rhs();

		lhs_var = lhs.get_var_id();
		rhs_var = rhs.get_var_id();

//		fprintf(dump_file,"\nlhs_var %d rhs_var %d\n", lhs_var, rhs_var);

		if ((!global_var(lhs_var)) && (lhs_var != ret_id) && (pars.find(lhs_var) == pars.end()) && (CDV.find(lhs_var) == CDV.end())) {
			continue;
		}

		temp_nodes.insert(lhs.get_node_id());
		temp_nodes.insert(rhs.get_node_id());

		dvg_size++;
//		e.print_edge();

		il1 = lhs.get_ind_list();

		if (CDV.find(lhs_var) != CDV.end() || CDV.find(rhs_var) != CDV.end()) {
//			fprintf(dump_file,"\nCDV\n");

			con_dep_edge++;

			if (il1.length() > 1) {
				deref_edge++;
			}

		} else {
			con_ind_edge++;

		}
	}

	int x;
	double z = 0.0;
	x = dvg_size; //con_ind_edge + con_dep_edge;

	if (x == 0)
		z = 0;
	else
		z = ((double) (con_ind_edge / dvg_size)) * 100;

	fprintf(dump_file, "\n=================================================================\n");
//	fprintf(dump_file,"\nDVG Details of Function %s\n", cgraph_node_name(cnode));
//	fprintf(dump_file,"\n=================================================================\n");
//	fprintf(dump_file,"\nOrder of Function %s in Worklist %d\n", cgraph_node_name(cnode), func_index_array[((function_info *)(cnode->aux))->func_num]);
//	fprintf(dump_file,"\nTransitive Callees of Function %s in Worklist %d\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->trans_callees.size());
//	fprintf(dump_file,"\nConstraints in the Function %s %d\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->cons_num);
//	fprintf(dump_file,"\nCall Statements in the Function %s %d\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->call_num);
//	fprintf(dump_file,"\nMaximum Call Depth in the Function %s %d\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->max_depth);
//	fprintf(dump_file,"\nTotal Size of DVG in terms of Edges %s %d\n", cgraph_node_name(cnode), temp_edges.size());
//	fprintf(dump_file,"\nTemporary Edges in DVG %s %d\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->get_fi_dvg().get_edge_list().size());
//	fprintf(dump_file,"\nFinal Size of DVG in terms of Edges %s %d\n", cgraph_node_name(cnode), dvg_size);
//	fprintf(dump_file,"\nFinal Size of DVG in terms of Nodes %s %d\n", cgraph_node_name(cnode), temp_nodes.size());
//	fprintf(dump_file,"\nContext Dependent Edges in DVG %s %d\n", cgraph_node_name(cnode), con_dep_edge);
//	fprintf(dump_file,"\nContext Independent Edges in DVG %s %d\n", cgraph_node_name(cnode), con_ind_edge);
//	fprintf(dump_file,"\nDeref on LHS of Edges in DVG %s %d\n", cgraph_node_name(cnode), deref_edge);

//	fprintf(dump_file,"\n\nNumber of Times Summary Constructed for Function %s is %d\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->count);
//	fprintf(dump_file,"\nnNumber of Times Function %s is  Called %d\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->use_count);

	fprintf(dump_file, "\nComplete Details of Function %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %lg\n", cnode->uid, func_index_array[((function_info *) (cnode->aux))->func_num], ((function_info *) (cnode->aux))->trans_callees.size(), ((function_info *) (cnode->aux))->cons_num, ((function_info *) (cnode->aux))->call_num, ((function_info *) (cnode->aux))->max_depth, temp_edges.size(), dvg_size, temp_nodes.size(), ((function_info *) (cnode->aux))->get_fi_dvg().get_edge_list().size(), con_dep_edge, con_ind_edge, deref_edge, ((function_info *) (cnode->aux))->count, ((function_info *) (cnode->aux))->use_count, z);

	fprintf(dump_file, "\n=================================================================\n");
}

void variation_in_sff(struct cgraph_node *cnode) {
	DVG prev_dvg, curr_dvg;

	basic_block endbb = end_bb_of_fn(cnode);

	prev_dvg = ((function_info *) (cnode->aux))->get_prev_dvg();
	curr_dvg = ((block_information *) (endbb->aux))->get_points_out();

	set_edges p_edges, c_edges;
	p_edges = prev_dvg.get_edge_list();
	c_edges = curr_dvg.get_edge_list();

	fprintf(dump_file, "\nAdditional Edges due to Fixed Point Computation is %d\n", c_edges.size() - p_edges.size());
}

void summary_construction() {
	struct cgraph_node *cnode;
	basic_block bb;

//	cnode_it = order_func.rbegin();

	fprintf(dump_file, "\nFunc_num %d\n", func_num);

//	while(!func_worklist.empty())
//	for(cnode_it; cnode_it != order_func.rend(); cnode_it++)

	while (!is_function_worklist_empty()) {
//		fprintf(dump_file,"\nHeeeee\n");

		for (int i = 1; i < func_count; i++)
//		for(int i = 0; i <= func_num; i++)
				{
			if (function_worklist[i]) {
				cnode = func_numbering[index_func_array[i]];
//				cnode = *cnode_it;
//				cnode = func_worklist.front();
//				func_it fit = func_worklist.begin();

//				fprintf(dump_file,"\nNumber of Times Function %s is called %d\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->count);

				function_worklist[i] = false;

//				func_worklist.erase(fit);
//				func_worklist.pop_front();

//  			      	fprintf(dump_file, "\nFunction %s:  Order in the Worklist %d\n", cgraph_node_name(cnode), i);
				fprintf(dump_file, "\n=======================================================================================\n");

#if 0
				list< struct cgraph_node * >::iterator fit;

				fprintf(dump_file,"\nFunction Worklist\n");
				for(fit = func_worklist.begin(); fit != func_worklist.end(); fit++)
				{
					fprintf(dump_file,"%s\t ", cgraph_node_name(*fit));
				}

				fprintf(dump_file,"\n");
#endif

#if STATS
				ptr_arith_count_stack = 0;
				ptr_arith_count_heap = 0;
#endif

				perform_analysis(cnode);

//				fprintf(dump_file,"\nHiiii\n");

				((function_info *) (cnode->aux))->count++;

#if STATS
//				fprintf(dump_file,"\nSummary Constructed for Function %s number of times %d\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->count);
//				fprintf(dump_file,"\nFunction Processed  for Worklist Management %s Position %d\n",cgraph_node_name(cnode), i);
//				fprintf(dump_file,"\nNumber of Additional Edges\n");
				if(((function_info *)(cnode->aux))->count > 1)
				variation_in_sff(cnode);
#endif

//				fprintf(dump_file,"\nHiiii\n");

				i = 0;

#if 0
				fprintf(dump_file,"\nFunction Processed  for Worklist Management %s Position %d\n",cgraph_node_name(cnode), i);
				fprintf(dump_file,"\nFunction Worklist\n");
				struct cgraph_node *c;
				unsigned int st = 0;

				for(int j = 0; j <= func_num; j++)
				{
					if(function_worklist[j])
					{
						c = func_numbering[index_func_array[j]];

						fprintf(dump_file,"%s\t",cgraph_node_name(c));
						st++;
					}
				}

//				fprintf(dump_file,"\n");
				fprintf(dump_file,"\nNumber of Functions in the Worklist %d\n",st);
#endif

#if 0 // STATS
				fprintf(dump_file,"\nPointer Arithmetic Count Stack %d\n",ptr_arith_count_stack);
				fprintf(dump_file,"\nPointer Arithmetic Count Heap %d\n",ptr_arith_count_heap);

				fprintf(dump_file,"\nCall Through Function Pointer %d\n",func_ptr_count);

//        			fprintf(dump_file, "\nFunction %s: \n", cgraph_node_name(cnode));
//				fprintf(dump_file,"\nTime Taken by Liveness %lg\n", liveness_time);
//				fprintf(dump_file,"\nTime Taken by Points-to %lg\n", points_to_time);
#endif
			}
		}
	}
}

void collect_data_measurements() {
	struct cgraph_node *cnode;

	unsigned int s_l, s_g, s_t, h_l, h_g, h_t;

	for (cnode = cgraph_nodes; cnode; cnode = cnode->next) {

		s_l = s_g = s_t = h_l = h_g = h_t = 0;

		if (!gimple_has_body_p(cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION(cnode->decl));

		basic_block bb = end_bb_of_fn(cnode);

//		fprintf(dump_file, "\nFunction %s Exit Block %d\n", cgraph_node_name(cnode), bb->index);

		DVG g_sens = ((block_information *) (bb->aux))->get_points_out();

		DVG g_insens = ((function_info *) (cnode->aux))->get_fi_dvg();

//		fprintf(dump_file,"\nDVG Flow Sensitive of Function\n");
//		g_sens.print_dvg();

//		fprintf(dump_file,"\nDVG Flow Insensitive of Function\n");
//		g_insens.print_dvg();

		set_edges elist1 = g_sens.get_edge_list();
		set_edges elist2 = g_insens.get_edge_list();

		edge_it eit;
		Edge e;

		for (eit = elist1.begin(); eit != elist1.end(); eit++) {
			e = get_edge(*eit);

			if (e.is_boundary_edge()) {
				continue;
			}

//			fprintf(dump_file,"\nEdge....\n");
//			e.print_edge();

			if (e.is_stack_edge()) {
				if (global_var(e.get_lhs().get_var_id())) {
//					fprintf(dump_file,"\ns_g++\n");

					++s_g;
				} else {
//					fprintf(dump_file,"\ns_l++\n");

					++s_l;
				}
			} else {
				if (global_var(e.get_lhs().get_var_id())) {
//					fprintf(dump_file,"\nh_g++\n");

					++h_g;
				} else {
//					fprintf(dump_file,"\nh_l++\n");

					++h_l;
				}

			}
		}

		for (eit = elist2.begin(); eit != elist2.end(); eit++) {
			e = get_edge(*eit);

//			fprintf(dump_file,"\nEdge....\n");
//			e.print_edge();

			if (e.is_stack_edge()) {
//				fprintf(dump_file,"\ns_t++\n");

				++s_t;
			} else {
//				fprintf(dump_file,"\nh_t++\n");

				++h_t;
			}
		}

		fprintf(dump_file, "\nStack - Local Edges %d\n", s_l);
		fprintf(dump_file, "\nStack - Global Edges %d\n", s_g);
		fprintf(dump_file, "\nStack - Temporary Edges %d\n", s_t);

		fprintf(dump_file, "\nHeap - Local Edges %d\n", h_l);
		fprintf(dump_file, "\nHeap - Global Edges %d\n", h_g);
		fprintf(dump_file, "\nHeap - Temporary Edges %d\n", h_t);

		pop_cfun();
	}
}

void get_size_of_dfv(struct cgraph_node *cnode) {
//	fprintf(dump_file,"\nStatistics of DVG of %s\n", cgraph_node_name(cnode));

	basic_block endbb = end_bb_of_fn(cnode);

	DVG callee_dvg = ((block_information *) (endbb->aux))->get_d_out();

	set_edges temp_edges = callee_dvg.get_edge_list();
	set_edges f_edges, diff_edges;
	il il1;

	fprintf(dump_file, "\n=================================================================\n");
	fprintf(dump_file, "\nDFV Details of Function %s\n", cgraph_node_name(cnode));
	fprintf(dump_file, "\n=================================================================\n");
	fprintf(dump_file, "\nOrder of Function %s in Worklist %d\n", cgraph_node_name(cnode), func_index_array[((function_info *) (cnode->aux))->func_num]);
	fprintf(dump_file, "\nDFV Size of Function %d is %d\n", cnode->uid, temp_edges.size());
	fprintf(dump_file, "\n=================================================================\n");
}

DVG get_in_d_info(basic_block bb, struct cgraph_node *cnode) {
	edge e;
	edge_iterator ei;
	int i;

	DVG g;

	if (((block_information *) (bb->aux))->start_block) {
//		fprintf(dump_file,"\nStart Block %d Function %s", bb->index, cgraph_node_name(cnode));
		return ((block_information *) (bb->aux))->get_d_in();
	}

	vector<DVG> dvg_list;
//	i = 0;

	FOR_EACH_EDGE(e,ei,bb->preds)
	{
//		fprintf(dump_file,"\nBasic Block %d\n", bb->index);
		basic_block bt = e->src;
//		fprintf(dump_file,"\nSuccessor Basic Block %d\n", bt->index);
//		i++;
		dvg_list.push_back(((block_information *) (bt->aux))->get_d_out());
	}
//	fprintf(dump_file,"\nNumber of Predecessors %d\n",i);

	if (dvg_list.size() == 1) {
//		fprintf(dump_file,"\nNo call to meet\n");
		return dvg_list[0];
	}

	g = dvg_list[0].meet(bb, dvg_list[1], cnode, true);

//	fprintf(dump_file,"\nMeet of G1 and G2 is \n");
//	fprintf(dump_file,"\nG1\n");
//	dvg_list[0].print_graph();
//	fprintf(dump_file,"\nG2\n");
//	dvg_list[1].print_graph();
//	fprintf(dump_file,"\nMeet G\n");
//	g.print_graph();

	for (i = 2; i < dvg_list.size(); i++) {
//		fprintf(dump_file,"\nMore than 2 predecessors\n");
		g = g.meet(bb, dvg_list[i], cnode, true);
	}

	return g;
}

void process_start_block_d(basic_block bb, struct cgraph_node *cnode) {
	struct cgraph_node *node;
	struct cgraph_edge *edge;
	basic_block endbb;
	DVG new_dvg, temp_dvg;
	set_edges temp_edges, edges;
	struct function *fn;

//	fprintf(dump_file,"\nFunction %s\n", cgraph_node_name(cnode));

#if 0
	for(edge = cnode->callers; edge; edge = edge->next_caller)
	{
		node = edge->caller;

		if (!gimple_has_body_p (node->decl) || node->clone_of)
		continue;

//		fprintf(dump_file,"\nCaller %s\n", cgraph_node_name(node));

		endbb = end_bb_of_fn(node);

		temp_dvg = ((block_information *)(endbb->aux))->get_d_out();

//		fprintf(dump_file,"\nCaller Data\n");
//		temp_dvg.print_dvg();

		temp_edges = temp_dvg.get_edge_list();

		edges.insert(temp_edges.begin(), temp_edges.end());
	}
#endif

	set_call_pts::iterator sit;

	sit = ((function_info *) (cnode->aux))->call_pts.begin();

	for (sit; sit != ((function_info *) (cnode->aux))->call_pts.end(); sit++) {
		node = func_numbering[get<0>(*sit)];

		fn = DECL_STRUCT_FUNCTION(node->decl);

		endbb = BASIC_BLOCK_FOR_FUNCTION(fn, get<1>(*sit));

		temp_dvg = ((block_information *) (endbb->aux))->get_d_in();

//		fprintf(dump_file,"\nCaller Data\n");
//		temp_dvg.print_dvg();

		temp_edges = temp_dvg.get_edge_list();

		edges.insert(temp_edges.begin(), temp_edges.end());

	}

	new_dvg.add_edges(bb, edges, cnode, 0, true);

//	basic_block startbb = start_bb_of_fn(cnode);

//	DVG b_in_prev, b_in;

//	b_in_prev = ((block_information *)(startbb->aux))->get_d_in();

	((block_information *) (bb->aux))->set_d_in(new_dvg);

//	fprintf(dump_file,"\nBoundary Information of %s\n",cgraph_node_name(cnode));
//	((block_information *)(bb->aux))->get_d_in().print_dvg();
//	new_dvg.print_dvg();

}

void process_block_d(basic_block bb, struct cgraph_node *cnode) {
	it ai;

	basic_block startbb = start_bb_of_fn(cnode);

	get_local_info(bb, cnode);

	DVG g_in_b = ((block_information *) (startbb->aux))->get_d_in();

	DVG g_in_f = ((block_information *) (bb->aux))->get_points_in();
	DVG g_out_f = ((block_information *) (bb->aux))->get_points_out();

	DVG g_in_d_new, g_out_d_new, g_in_d, g_out_d;

	DVG g_in_d_prev = ((block_information *) (bb->aux))->get_d_in();
	DVG g_out_d_prev = ((block_information *) (bb->aux))->get_d_out();

	g_in_d_new = g_in_b.copy_dvg();
	g_out_d_new = g_in_b.copy_dvg();

	struct cgraph_node *node;
	node = NULL;

	set_edges elist, temp, remove;
	edge_it eit;
	Edge e;
	map<edge_id, unsigned int> local_in, local_out, rev_temp_map;
	map<unsigned int, set_edges> flow_sens_in, flow_sens_out;
	map<unsigned int, set_edges>::iterator mit;

	local_in = ((block_information *) (bb->aux))->order_in;
	local_out = ((block_information *) (bb->aux))->order_out;

	rev_temp_map = ((function_info *) (cnode->aux))->get_rev_order_map();

	unsigned int order, con_id;
	unsigned int lhs_var, rhs_var, var;
	Node lhs, rhs;

	set<unsigned int> pars = ((function_info *) (cnode->aux))->get_params();
	unsigned int ret_id = ((function_info *) (cnode->aux))->get_ret_id();

	// Do Function Composition

	elist = g_in_f.get_edge_list();

	for (eit = elist.begin(); eit != elist.end(); eit++) {
		e = get_edge(*eit);

		if (e.is_boundary_edge()) {
			continue;
		}

		if (local_in[*eit] == 0) {
			order = rev_temp_map[*eit];
		} else {
			order = local_in[*eit];
		}

		temp = flow_sens_in[order];
		temp.insert(*eit);
		flow_sens_in[order] = temp;
	}

	for (mit = flow_sens_in.begin(); mit != flow_sens_in.end(); mit++) {
		temp = mit->second;

		con_id = mit->first;

		for (eit = temp.begin(); eit != temp.end(); eit++) {
			e = get_edge(*eit);

//			fprintf(dump_file,"\nEdge from Callee DVG\n");
//			e.print_edge();

			if (e.is_boundary_edge()) {
//				fprintf(dump_file,"\nBoundary Edge\n");
				continue;
			}

//			fprintf(dump_file,"\nHiii\n");

			lhs_var = e.get_lhs().get_var_id();

			if ((!global_var(lhs_var)) && (lhs_var != ret_id) && (pars.find(lhs_var) == pars.end()) && (CDV.find(lhs_var) == CDV.end())) {
				continue;
			}

			lhs = e.get_lhs();
			rhs = e.get_rhs();

			var = lhs.get_var_id();

			if (CDV.find(var) != CDV.end()) {

				lhs.set_var_id(var - 1);
				lhs.add_node_map();
			}

			var = rhs.get_var_id();

			if (CDV.find(var) != CDV.end()) {
				rhs.set_var_id(var - 1);
				rhs.add_node_map();
			}

			Edge e_temp(lhs, rhs);

			g_in_d_new.func_comp(bb, e_temp, cnode, con_id, g_in_f, node, true);
		}
	}

	// OUT Composition

	elist = g_out_f.get_edge_list();

	for (eit = elist.begin(); eit != elist.end(); eit++) {
		e = get_edge(*eit);

		if (e.is_boundary_edge()) {
			continue;
		}

		if (local_out[*eit] == 0) {
			order = rev_temp_map[*eit];
		} else {
			order = local_out[*eit];
		}

		temp = flow_sens_out[order];
		temp.insert(*eit);
		flow_sens_out[order] = temp;
	}

	for (mit = flow_sens_out.begin(); mit != flow_sens_out.end(); mit++) {
		temp = mit->second;

		con_id = mit->first;

		for (eit = temp.begin(); eit != temp.end(); eit++) {
			e = get_edge(*eit);

//			fprintf(dump_file,"\nEdge from Callee DVG\n");
//			e.print_edge();

			if (e.is_boundary_edge()) {
//				fprintf(dump_file,"\nBoundary Edge\n");
				continue;
			}

//			fprintf(dump_file,"\nHiii\n");

			lhs_var = e.get_lhs().get_var_id();

			if ((!global_var(lhs_var)) && (lhs_var != ret_id) && (pars.find(lhs_var) == pars.end()) && (CDV.find(lhs_var) == CDV.end())) {
				continue;
			}

			lhs = e.get_lhs();
			rhs = e.get_rhs();

			var = lhs.get_var_id();

			if (CDV.find(var) != CDV.end()) {

				lhs.set_var_id(var - 1);
				lhs.add_node_map();
			}

			var = rhs.get_var_id();

			if (CDV.find(var) != CDV.end()) {
				rhs.set_var_id(var - 1);
				rhs.add_node_map();
			}

			Edge e_temp(lhs, rhs);

			g_out_d_new.func_comp(bb, e_temp, cnode, con_id, g_out_f, node, true);
		}
	}

	// After Function Composition

//	fprintf(dump_file,"\nAfter Printing DVG IN\n");

	live_info l_out = ((block_information *) (bb->aux))->get_live_out();

	live_type temp_live = l_out.get_l_info();

#if LIVENESS

	elist = g_in_d_new.get_edge_list();

	for(eit = elist.begin(); eit != elist.end(); eit++)
	{
		e = get_edge(*eit);
		lhs = e.get_lhs();
		lhs_var = lhs.get_var_id();

		if(CDV.find(lhs.get_var_id()) == CDV.end())
		{
			if((!global_var(lhs_var)) && (temp_live.find(lhs_var) == temp_live.end()) && (lhs_var != ret_id) && (pars.find(lhs_var) == pars.end()))
			{
				remove.insert(*eit);
			}
		}
	}

	g_in_d_new.remove_edges(bb, remove, cnode, true);
	remove.clear();

	elist = g_out_d_new.get_edge_list();

	for(eit = elist.begin(); eit != elist.end(); eit++)
	{
		e = get_edge(*eit);
		lhs = e.get_lhs();
		lhs_var = lhs.get_var_id();

		if(CDV.find(lhs.get_var_id()) == CDV.end())
		{
			if((!global_var(lhs_var)) && (temp_live.find(lhs_var) == temp_live.end()) && (lhs_var != ret_id) && (pars.find(lhs_var) == pars.end()))
			{
				remove.insert(*eit);
			}
		}
	}

	g_out_d_new.remove_edges(bb, remove, cnode, true);
#endif

	g_in_d = g_in_d_new; // .meet(bb, g_in_d_new, cnode, true);
//	g_in_d = g_in_d_prev.meet(bb, g_in_d_new, cnode, true);
	((block_information *) (bb->aux))->set_d_in(g_in_d);

	fprintf(dump_file, "\nDVG IN DFV\n");
	g_in_d.print_dvg();

	g_out_d = g_out_d_new; // .meet(bb, g_out_d_new, cnode, true);
//	g_out_d = g_out_d_prev.meet(bb, g_out_d_new, cnode, true);
	((block_information *) (bb->aux))->set_d_out(g_out_d);

	if (((block_information *) (bb->aux))->dinitialized == 1) {
		((block_information *) (bb->aux))->set_d_out(g_out_d);
		get_succ_basic_block(bb, cnode);
		((block_information *) (bb->aux))->dinitialized = 0;
		fprintf(dump_file, "\nDVG OUT DFV\n");
//		fprintf(dump_file, "\n\nDFunction %s Other Block No %d ", cgraph_node_name(cnode), bb->index);
		g_out_d.print_dvg();

#if 1
//		if(((function_info *)(cnode->aux))->count > 3)   // Function composition with no kill if function is being processed more than twice
		{
			if (end_bb_of_fn(cnode)->index == bb->index) // This is the Exit Block
			{
				struct cgraph_edge *edge;
				struct cgraph_node *node;
				struct function *fn;
				basic_block call_block;

				list<struct cgraph_node *> temp_func;
				list<struct cgraph_node *>::iterator tfit;

				for (edge = cnode->callees; edge; edge = edge->next_callee) {
					node = edge->callee;

					if (!gimple_has_body_p(node->decl) || node->clone_of)
						continue;

					if (find(temp_func.begin(), temp_func.end(), node) == temp_func.end()) {
						temp_func.push_back(node);
					}
				}

				for (tfit = temp_func.begin(); tfit != temp_func.end(); tfit++) {
					node = *tfit;

//				if(!function_worklist_d[func_index_array_d[((function_info *)(node->aux))->func_num]])
//					fprintf(dump_file,"\nPush Caller on Worklist %s due to Processing Function %s Order in the Worklist \n",cgraph_node_name(node), cgraph_node_name(cnode), func_index_array_d[((function_info *)(node->aux))->func_num]);

					function_worklist_d[func_index_array_d[((function_info *) (node->aux))->func_num]] = true;
					((function_info *) (node->aux))->points_worklist[0] = true;
				}

			}
		}
#endif
	} else {
#if STATS
		gcomp_count++;

//		fprintf(dump_file,"\nGraph Comparison Count so far %d\n", gcomp_count);
#endif

		if (!(g_out_d_prev == g_out_d)) {
//			fprintf(dump_file,"\nDVG OUT Changed\n");
//			fprintf(dump_file,"\nPrev DVG OUT\n");
//			g_out_prev.print_dvg();
//			fprintf(dump_file,"\nNew DVG OUT\n");
//			g_out.print_dvg();

			if (!g_out_d.weaker(g_out_d_prev, cnode)) {
				fprintf(dump_file, "\nNot a Valid Operation - Non-Monotone\n");

//				fprintf(dump_file,"\ng_out\n");
//				g_out.print_dvg();

//				fprintf(dump_file,"\ng_out_prev\n");
//				g_out_prev.print_dvg();
			}

			((block_information *) (bb->aux))->set_d_out(g_out_d);
			get_succ_basic_block(bb, cnode);
			fprintf(dump_file, "\nDVG OUT DFV\n");
//			fprintf(dump_file, "\n\nDFunction %s Other Block No %d ", cgraph_node_name(cnode), bb->index);
			g_out_d.print_dvg();

#if 1
//			if(((function_info *)(cnode->aux))->count > 3)   // Function composition with no kill if function is being processed more than twice
			{
				if (end_bb_of_fn(cnode)->index == bb->index) // This is the Exit Block
				{
					struct cgraph_edge *edge;
					struct cgraph_node *node;
					struct function *fn;
					basic_block call_block;

					list<struct cgraph_node *> temp_func;
					list<struct cgraph_node *>::iterator tfit;

					for (edge = cnode->callees; edge; edge = edge->next_callee) {
						node = edge->callee;

						if (!gimple_has_body_p(node->decl) || node->clone_of)
							continue;

						if (find(temp_func.begin(), temp_func.end(), node) == temp_func.end()) {
							temp_func.push_back(node);
						}
					}

					for (tfit = temp_func.begin(); tfit != temp_func.end(); tfit++) {
						node = *tfit;

//					if(!function_worklist_d[func_index_array_d[((function_info *)(node->aux))->func_num]])
//						fprintf(dump_file,"\nPush Caller on Worklist %s due to Processing Function %s Order in the Worklist \n",cgraph_node_name(node), cgraph_node_name(cnode), func_index_array_d[((function_info *)(node->aux))->func_num]);

						function_worklist_d[func_index_array_d[((function_info *) (node->aux))->func_num]] = true;

						((function_info *) (node->aux))->points_worklist[0] = true;

//					fprintf(dump_file,"\nIndex %d\n", func_index_array_d[((function_info *)(node->aux))->func_num]);

//					fprintf(dump_file,"\nKasa Kay\n");

					}
				}
			}
#endif
		}
	}
}

void process_intra_block_d_bb(basic_block bb, struct cgraph_node *cnode) {
	it ai;

//	fprintf(dump_file,"\nIn dfv3 kasa kay\n");

	get_local_info(bb, cnode);

	DVG g_in_prev_d = ((block_information *) (bb->aux))->get_d_in();

	DVG g_in_new_d = get_in_d_info(bb, cnode);

	DVG g_in_d = g_in_new_d;

	((block_information *) (bb->aux))->set_d_in(g_in_d);

	fprintf(dump_file, "\nDFV IN\n");
	g_in_d.print_dvg();

	DVG g_out_d, g_out_prev_d, g_out_new_d;

	g_out_prev_d = ((block_information *) (bb->aux))->get_d_out();
	g_out_new_d = g_in_d.copy_dvg();

	DVG g_f = ((block_information *) (bb->aux))->get_summ();

	struct cgraph_node *node;
	node = NULL;

	set_edges elist, temp, remove;
	edge_it eit;
	Edge e;

	unsigned int order, con_id;
	unsigned int lhs_var, rhs_var, var;
	Node lhs, rhs;

	set<unsigned int> pars = ((function_info *) (cnode->aux))->get_params();
	unsigned int ret_id = ((function_info *) (cnode->aux))->get_ret_id();

	// Do Function Composition

	// OUT Composition

	elist = g_f.get_edge_list();

	for (eit = elist.begin(); eit != elist.end(); eit++) {
		e = get_edge(*eit);

//		fprintf(dump_file,"\nEdge from Callee DVG\n");
//		e.print_edge();

		if (e.is_boundary_edge()) {
//			fprintf(dump_file,"\nBoundary Edge\n");
			continue;
		}

//		fprintf(dump_file,"\nHiii\n");

		lhs_var = e.get_lhs().get_var_id();

//		if((!global_var(lhs_var)) && (lhs_var != ret_id) && (pars.find(lhs_var) == pars.end()) && (CDV.find(lhs_var) == CDV.end()))
//		{
//			continue;
//		}

		lhs = e.get_lhs();
		rhs = e.get_rhs();

		var = lhs.get_var_id();

		if (CDV.find(var) != CDV.end()) {
			lhs.set_var_id(var - 1);
			lhs.add_node_map();
		}

		var = rhs.get_var_id();

		if (CDV.find(var) != CDV.end()) {
			rhs.set_var_id(var - 1);
			rhs.add_node_map();
		}

		Edge e_temp(lhs, rhs);

		g_out_new_d.func_comp(bb, e_temp, cnode, con_id, g_f, node, true);
	}

	// After Function Composition

//	fprintf(dump_file,"\nAfter Printing DVG IN\n");

	live_info l_out = ((block_information *) (bb->aux))->get_live_out();

	live_type temp_live = l_out.get_l_info();

#if LIVENESS

	elist = g_out_new_d.get_edge_list();

	for(eit = elist.begin(); eit != elist.end(); eit++)
	{
		e = get_edge(*eit);
		lhs = e.get_lhs();
		lhs_var = lhs.get_var_id();

		if(CDV.find(lhs.get_var_id()) == CDV.end())
		{
			if((!global_var(lhs_var)) && (temp_live.find(lhs_var) == temp_live.end()) && (lhs_var != ret_id) && (pars.find(lhs_var) == pars.end()))
			{
				remove.insert(*eit);
			}
		}
	}

	g_out_new_d.remove_edges(bb, remove, cnode, true);
#endif

	g_out_d = g_out_new_d;
	((block_information *) (bb->aux))->set_d_out(g_out_d);

	if (((block_information *) (bb->aux))->dinitialized == 1) {
		((block_information *) (bb->aux))->set_d_out(g_out_d);
		get_succ_basic_block(bb, cnode);
		((block_information *) (bb->aux))->dinitialized = 0;
		fprintf(dump_file, "\nDVG OUT DFV\n");
//		fprintf(dump_file, "\n\nDFunction %s Other Block No %d ", cgraph_node_name(cnode), bb->index);
		g_out_d.print_dvg();

#if 1
//		if(((function_info *)(cnode->aux))->count > 3)   // Function composition with no kill if function is being processed more than twice
		{
			if (end_bb_of_fn(cnode)->index == bb->index) // This is the Exit Block
			{
				struct cgraph_edge *edge;
				struct cgraph_node *node;
				struct function *fn;
				basic_block call_block;

				list<struct cgraph_node *> temp_func;
				list<struct cgraph_node *>::iterator tfit;

				for (edge = cnode->callees; edge; edge = edge->next_callee) {
					node = edge->callee;

					if (!gimple_has_body_p(node->decl) || node->clone_of)
						continue;

					if (find(temp_func.begin(), temp_func.end(), node) == temp_func.end()) {
						temp_func.push_back(node);
					}
				}

				for (tfit = temp_func.begin(); tfit != temp_func.end(); tfit++) {
					node = *tfit;

					function_worklist_d[func_index_array_d[((function_info *) (node->aux))->func_num]] = true;
					((function_info *) (node->aux))->points_worklist[0] = true;
				}

			}
		}
#endif
	} else {
#if STATS
		gcomp_count++;

//		fprintf(dump_file,"\nGraph Comparison Count so far %d\n", gcomp_count);
#endif

		if (!(g_out_prev_d == g_out_d)) {
//			fprintf(dump_file,"\nDVG OUT Changed\n");
//			fprintf(dump_file,"\nPrev DVG OUT\n");
//			g_out_prev.print_dvg();
//			fprintf(dump_file,"\nNew DVG OUT\n");
//			g_out.print_dvg();

			if (!g_out_d.weaker(g_out_prev_d, cnode)) {
				fprintf(dump_file, "\nNot a Valid Operation - Non-Monotone\n");

//				fprintf(dump_file,"\ng_out\n");
//				g_out.print_dvg();

//				fprintf(dump_file,"\ng_out_prev\n");
//				g_out_prev.print_dvg();
			}

			((block_information *) (bb->aux))->set_d_out(g_out_d);
			get_succ_basic_block(bb, cnode);
			fprintf(dump_file, "\nDVG OUT DFV\n");
//			fprintf(dump_file, "\n\nDFunction %s Other Block No %d ", cgraph_node_name(cnode), bb->index);
			g_out_d.print_dvg();

#if 1
//			if(((function_info *)(cnode->aux))->count > 3)   // Function composition with no kill if function is being processed more than twice
			{
				if (end_bb_of_fn(cnode)->index == bb->index) // This is the Exit Block
				{
					struct cgraph_edge *edge;
					struct cgraph_node *node;
					struct function *fn;
					basic_block call_block;

					list<struct cgraph_node *> temp_func;
					list<struct cgraph_node *>::iterator tfit;

					for (edge = cnode->callees; edge; edge = edge->next_callee) {
						node = edge->callee;

						if (!gimple_has_body_p(node->decl) || node->clone_of)
							continue;

						if (find(temp_func.begin(), temp_func.end(), node) == temp_func.end()) {
							temp_func.push_back(node);
						}
					}

					for (tfit = temp_func.begin(); tfit != temp_func.end(); tfit++) {
						node = *tfit;

						function_worklist_d[func_index_array_d[((function_info *) (node->aux))->func_num]] = true;

						((function_info *) (node->aux))->points_worklist[0] = true;

					}
				}
			}
#endif
		}
	}
}

void process_intra_block_d(basic_block bb, struct cgraph_node *cnode) {
//	fprintf(dump_file,"\nInside process_intra_block_d\n");

	it ai;

	get_local_info(bb, cnode);

	DVG g_in_prev_d = ((block_information *) (bb->aux))->get_d_in();

	DVG g_in_new_d = get_in_d_info(bb, cnode);

	DVG g_in_d = g_in_new_d;

	((block_information *) (bb->aux))->set_d_in(g_in_d);

	fprintf(dump_file, "\nDFV IN\n");
	g_in_d.print_dvg();

	DVG g_out_d, g_out_prev_d, g_out_new_d;

	g_out_prev_d = ((block_information *) (bb->aux))->get_d_out();
	g_out_new_d = g_in_d.copy_dvg();

	live_info l_out = ((block_information *) (bb->aux))->get_live_out();

	live_type temp_live = l_out.get_l_info();

	DVG out;

	constraint_list con = ((block_information *) (bb->aux))->get_list();

	for (ai = con.begin(); ai != con.end(); ai++) {

		if (!(*ai).get_bool())
			continue;

		constraint_t cons = VEC_index(constraint_t, aliases, (*ai).get_int());

		g_out_new_d.generate_graph(bb, cons, cnode, (*ai).get_int());
	}

#if LIVENESS
	set_edges elist, remove;

	elist = g_out_new_d.get_edge_list();

	edge_it eit;
	Edge e;
	Node lhs;
	unsigned int lhs_var;

	set<unsigned int> pars = ((function_info *)(cnode->aux))->get_params();
	unsigned int ret_id = ((function_info *)(cnode->aux))->get_ret_id();

	for(eit = elist.begin(); eit != elist.end(); eit++)
	{
		e = get_edge(*eit);
		lhs = e.get_lhs();
		lhs_var = lhs.get_var_id();

		if(CDV.find(lhs.get_var_id()) == CDV.end())
		{
			if((!global_var(lhs_var)) && (temp_live.find(lhs_var) == temp_live.end()) && (lhs_var != ret_id) && (pars.find(lhs_var) == pars.end()))
			{
//				fprintf(dump_file,"\nEdge Removed due to Liveness\n");
//				e.print_edge();
				remove.insert(*eit);
			}
		}
	}

	g_out_new_d.remove_edges(bb, remove, cnode, false);
#endif

	if (((block_information *) (bb->aux))->dinitialized == 1) {
//		fprintf(dump_file,"\nGet succs\n");
		g_out_d = g_out_new_d;

		((block_information *) (bb->aux))->set_d_out(g_out_d);
		get_succ_basic_block(bb, cnode);
		((block_information *) (bb->aux))->dinitialized = 0;
		fprintf(dump_file, "\nDFV OUT\n");
//		fprintf(dump_file, "\n\nDFunction %s Other Block No %d ", cgraph_node_name(cnode), bb->index);
		g_out_d.print_dvg();

#if 1
//		if(((function_info *)(cnode->aux))->count > 3)   // Function composition with no kill if function is being processed more than twice
		{
			if (end_bb_of_fn(cnode)->index == bb->index) // This is the Exit Block
			{
				struct cgraph_edge *edge;
				struct cgraph_node *node;
				struct function *fn;
				basic_block call_block;

				list<struct cgraph_node *> temp_func;
				list<struct cgraph_node *>::iterator tfit;

				for (edge = cnode->callees; edge; edge = edge->next_callee) {
					node = edge->callee;

					if (!gimple_has_body_p(node->decl) || node->clone_of)
						continue;

					if (find(temp_func.begin(), temp_func.end(), node) == temp_func.end()) {
						temp_func.push_back(node);
					}
				}

				for (tfit = temp_func.begin(); tfit != temp_func.end(); tfit++) {
					node = *tfit;

					function_worklist[func_index_array[((function_info *) (node->aux))->func_num]] = true;

					((function_info *) (node->aux))->points_worklist[0] = true;
				}
			}
		}
#endif
	} else {
		g_out_d = g_out_new_d;

#if STATS
		gcomp_count++;

//		fprintf(dump_file,"\nGraph Comparison Count so far %d\n", gcomp_count);
#endif

		if (!(g_out_prev_d == g_out_d)) {
//			fprintf(dump_file,"\nDVG OUT Changed\n");
//			fprintf(dump_file,"\nPrev DVG OUT\n");
//			g_out_prev.print_dvg();
//			fprintf(dump_file,"\nNew DVG OUT\n");
//			g_out.print_dvg();

			((block_information *) (bb->aux))->set_d_out(g_out_d);
			get_succ_basic_block(bb, cnode);
			fprintf(dump_file, "\nDFV OUT\n");
//			fprintf(dump_file, "\n\nDFunction %s Other Block No %d ", cgraph_node_name(cnode), bb->index);
			g_out_d.print_dvg();

			if (!g_out_d.weaker(g_out_prev_d, cnode)) {
				fprintf(dump_file, "\nNot a Valid Operation - Non-Monotone\n");

//				fprintf(dump_file,"\ng_out\n");
//				g_out.print_dvg();

//				fprintf(dump_file,"\ng_out_prev\n");
//				g_out_prev.print_dvg();
			}

#if 1
//			if(((function_info *)(cnode->aux))->count > 3)   // Function composition with no kill if function is being processed more than twice
			{
				if (end_bb_of_fn(cnode)->index == bb->index) // This is the Exit Block
				{
					struct cgraph_edge *edge;
					struct cgraph_node *node;
					struct function *fn;
					basic_block call_block;

					list<struct cgraph_node *> temp_func;
					list<struct cgraph_node *>::iterator tfit;

					for (edge = cnode->callees; edge; edge = edge->next_callee) {
						node = edge->callee;

						if (!gimple_has_body_p(node->decl) || node->clone_of)
							continue;

						if (find(temp_func.begin(), temp_func.end(), node) == temp_func.end()) {
							temp_func.push_back(node);
						}
					}

					for (tfit = temp_func.begin(); tfit != temp_func.end(); tfit++) {
						node = *tfit;

						function_worklist[func_index_array[((function_info *) (node->aux))->func_num]] = true;

						((function_info *) (node->aux))->points_worklist[0] = true;
					}
				}
			}
#endif
		}
	}
}

void do_points_to_d(struct cgraph_node *cnode) {
	fprintf(dump_file, "\n=========================Data Flow Pass %s  Order %d ==============================\n", cgraph_node_name(cnode), cnode->uid);

	struct function *fn;

	fn = DECL_STRUCT_FUNCTION(cnode->decl);

	int i;
	unsigned int nbb = ((function_info *) (cnode->aux))->get_num_bb();

	basic_block bb;

	while (!(((function_info *) (cnode->aux))->is_empty_worklist(2))) {
		for (i = 0; i < nbb; i++) {
			if (((function_info *) (cnode->aux))->points_worklist[i]) {
				bb = BASIC_BLOCK_FOR_FUNCTION(fn, ((function_info * )(cnode->aux))->rev_post_order[i]);

				if (((block_information *) (bb->aux))->start_block) {
					fprintf(dump_file, "\nFunction %s Start Block No %d\n", cgraph_node_name(cnode), bb->index);
					process_start_block_d(bb, cnode);
					((function_info *) (cnode->aux))->points_worklist[i] = false;

#if 0
#if DFVSFFALL
					process_block_d(bb, cnode);
#endif

#if DFVSFFCALL
					process_intra_block_d(bb,cnode);
#endif
#endif
				}

				if (((block_information *) (bb->aux))->call_block) {
					fprintf(dump_file, "\nFunction %s Call Block No %d\n", cgraph_node_name(cnode), bb->index);
					process_block_d(bb, cnode);
					((function_info *) (cnode->aux))->points_worklist[i] = false;
				} else {
					fprintf(dump_file, "\n\nFunction %s Other Block No %d ", cgraph_node_name(cnode), bb->index);

#if DFVSFFALL
					process_block_d(bb,cnode);
#endif

#if DFVSFFCALL
					process_intra_block_d(bb,cnode);
#endif

#if DFVSFFCALLBB
					process_intra_block_d_bb(bb,cnode);
#endif

					((function_info *) (cnode->aux))->points_worklist[i] = false;
//					fprintf(dump_file, "\n\nFunction %s Other Block No %d ", cgraph_node_name(cnode), bb->index);
//					((block_information *)(bb->aux))->get_points_out().print_dvg();
				}
			}
		}
	}
}

void perform_analysis_d(struct cgraph_node *cnode) {
#if STATS
	starttime();
#endif

	do_points_to_d(cnode);

#if STATS
	ttime = stoptime();

	points_to_time_d += ttime;

//	fprintf(dump_file,"\nPoints-to DFV Pass for Function %s, Overall Time %lg, Time Taken for this Computation %lg\n", cgraph_node_name(cnode), points_to_time_d, ttime);
#endif

	((function_info *) (cnode->aux))->set_dvisited(true);
}

void data_flow_value_computation() {
	struct cgraph_node *cnode;
	basic_block bb;

//	fprintf(dump_file,"\nFunc_num %d\n",func_num);

	while (!is_function_worklist_d_empty()) {
//		fprintf(dump_file,"\nHeeeee\n");

		for (int i = 1; i < func_count_d; i++)
//		for(int i = 0; i <= func_num; i++)
				{
			if (function_worklist_d[i]) {
				cnode = func_numbering[index_func_array_d[i]];

//				fprintf(dump_file,"\nNumber of Times Function %s is called %d\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->count);

				function_worklist_d[i] = false;

//  			      	fprintf(dump_file, "\nFunction %s:  Order in the Worklist %d\n", cgraph_node_name(cnode), i);
//			        fprintf(dump_file, "\n=======================================================================================\n");

				perform_analysis_d(cnode);

				((function_info *) (cnode->aux))->dcount++;

				i = -1;

#if 0
				fprintf(dump_file,"\nFunction Processed %s\n",cgraph_node_name(cnode));
				fprintf(dump_file,"\nFunction Worklist\n");
				struct cgraph_node *c;
				unsigned int st = 0;

				for(int j = 0; j <= func_num; j++)
				{
					if(function_worklist[j])
					{
						c = func_numbering[index_func_array[j]];

						fprintf(dump_file,"%s\t",cgraph_node_name(c));
						st++;
					}
				}

//				fprintf(dump_file,"\n");

				fprintf(dump_file,"\nNumber of Functions in the Worklist %d\n",st);
#endif

			}
		}
	}

}

void get_bb_info() {
	fprintf(dump_file, "\n=========================Information of main ==============================\n");

	struct function *fn;

	fn = DECL_STRUCT_FUNCTION(main_cnode->decl);

	int i;
	unsigned int nbb = ((function_info *) (main_cnode->aux))->get_num_bb();

	basic_block bb;
	DVG g;
	set_edges edges;

	for (i = 0; i < nbb; i++) {
		bb = BASIC_BLOCK_FOR_FUNCTION(fn, ((function_info * )(main_cnode->aux))->rev_post_order[i]);

		g = ((block_information *) (bb->aux))->get_points_out();

		edges = g.get_edge_list();

		fprintf(dump_file, "\nSize of DVG %d Distance d from Start Node %d\n", edges.size(), i + 1);
	}
}

bool ignore_constraint(constraint_t con) {
	fprintf(dump_file, "\nInside ignore_constraint\n");

	fprintf(dump_file, "\nBefore 1st check\n");
	if (con->lhs.offset != 0 || con->rhs.offset != 0) {
		return false;
	}
	fprintf(dump_file, "\nAfter 1st check\n");

	tree lhs, rhs;

	lhs = VEC_index(csvarinfo_t,csvarmap,con->lhs.var)->decl;
	rhs = VEC_index(csvarinfo_t,csvarmap,con->rhs.var)->decl;

	print_node(dump_file, "\nNode Info\n", lhs, 0);
	print_node(dump_file, "\nNode Info\n", rhs, 0);

	fprintf(dump_file, "\nBefore 2nd check\n");
	if (TREE_TYPE(lhs) && TREE_TYPE(TREE_TYPE(lhs)) && TREE_CODE (TREE_TYPE (TREE_TYPE(lhs))) == RECORD_TYPE || TREE_CODE(lhs) == COMPONENT_REF) {
		return false;
	}
	fprintf(dump_file, "\nAfter 2nd check\n");
	fprintf(dump_file, "\nBefore 3rd check\n");

#if 0
	if (TREE_TYPE(rhs) != NULL) // && TREE_TYPE(TREE_TYPE(rhs)))
	{
		fprintf(dump_file, "\nBefore 2..25 check\n");
		if(TREE_TYPE(TREE_TYPE(rhs)))
		{
			fprintf(dump_file, "\nBefore 2.25 check\n");
			fprintf(dump_file, "\nBefore 2.5 check\n");
			if(TREE_CODE (TREE_TYPE (TREE_TYPE(rhs))) == RECORD_TYPE) // || TREE_CODE(rhs) == COMPONENT_REF)
			{
				fprintf(dump_file, "\nAfter 2.5 check\n");
				return false;
			}
		}
	}
#endif
	fprintf(dump_file, "\nAfter 3rd check\n");

	return true;
}

void accessing_constraints() {
	constraint_t con;
	int lhs_type, rhs_type;
	int lhs_var_id, rhs_var_id;
	const char *lhs_op, *rhs_op;
	csvarinfo_t lhs, rhs;

	for (int i = 0; i < VEC_length(constraint_t, aliases); i++) {
		con = VEC_index(constraint_t, aliases, i);

		lhs_type = con->lhs.type;
		rhs_type = con->rhs.type;
		lhs_var_id = con->lhs.var;
		rhs_var_id = con->rhs.var;
		lhs = VEC_index(csvarinfo_t, csvarmap, lhs_var_id);
		rhs = VEC_index(csvarinfo_t, csvarmap, rhs_var_id);
		lhs_op = lhs->name;
		rhs_op = rhs->name;
		//fprintf(dump_file,"\nConstraint index: %d LHS Op: %s LHS type: %d LHS ID: %d \n RHS Op: %s RHS type: %d RHS ID: %d \n",
		//	i,lhs_op,lhs_type,lhs_var_id, rhs_op,rhs_type, rhs_var_id);
	}
	//fprintf(dump_file,"Length of vector: %d \n",VEC_length (constraint_t, aliases));
}

// Vini, June'15
void generate_call_return_constraints(Allptsinfo & obj_allptinfo) {
	//fprintf (dump_file, "\ngenerate_call_return_constraints");
	struct cgraph_node * cnode;

	for (cnode = cgraph_nodes; cnode; cnode = cnode->next) {
		/* Nodes without a body, and clone nodes are not interesting. */
		if (!gimple_has_body_p(cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION(cnode->decl));

		basic_block bb;
		FOR_EACH_BB (bb)
		{
			gimple_stmt_iterator gsi;
			for (gsi = gsi_start_bb(bb); !gsi_end_p(gsi); gsi_next(&gsi)) {
				gimple stmt = gsi_stmt(gsi);
				if (!is_gimple_call(stmt))
					continue;

				Pointee_Set callees;

				tree callee_decl = gimple_call_fndecl(stmt);
				// If it is not function pointer
				if (callee_decl) {
					// Skip library calls
					if (!DECL_STRUCT_FUNCTION(callee_decl))
						continue;

					csvarinfo_t callee_info = cs_get_vi_for_tree(callee_decl, bb, cnode);
					callees.insert(callee_info->id);
					//fprintf (dump_file, "\nFunction call %s (%d): ", callee_info->name, callee_info->id);
				}
				// If it is a function pointer
				else {
					tree fp_decl = gimple_call_fn(stmt);
					if (!fp_decl) {
						fprintf(dump_file, "\nError: Could not fetch fp");
						return;
					}
					csvarinfo_t fp_info = cs_get_vi_for_tree(fp_decl, bb, cnode);
					//fprintf (dump_file, "\nFunction pointer %s (%d): ", fp_info->name, fp_info->id);
					PSet callees_obj = obj_allptinfo.get_pointee_set_object(fp_info->id);
					//callees_obj.displayset ();
					callees = callees_obj.get_st();
				}
				Pointee_Set::iterator cit;
				for (cit = callees.begin(); cit != callees.end(); cit++) {
					int callee_id = *cit;
					if (!is_proper_var(callee_id))
						continue;

					csvarinfo_t callee_info = VEC_index(csvarinfo_t, csvarmap, callee_id);
					//fprintf (dump_file, "%s (%d), ", callee_info->name, callee_info->id);
					if (!callee_info->decl || callee_info->is_heap_var)
						continue;
					if (TREE_CODE (callee_info->decl) != FUNCTION_DECL)
						continue;

					//fprintf (dump_file, "\ncallee exists");
					struct cgraph_node * callee = cgraph_get_node(callee_info->decl);
					//fprintf (dump_file, "\ncallee node retrieved");
					basic_block callee_end_block = end_bb_of_fn(callee);
					//fprintf (dump_file, "\nend block retrieved");

					// Map function arguments with parameters
					map_function_arguments(cnode, bb, stmt, callee);

					// Map return value with received variable
					map_return_value(cnode, bb, callee_end_block, callee);
				}
			}
		}
		pop_cfun();
	}
	//fprintf (dump_file, "\nDone generate_call_return_constraints\n");
}

void call_process_inputs(Allptsinfo & obj_allptinfo) {

	constraint_t con;
	int lhs_type, rhs_type;
	int lhs_var_id, rhs_var_id;
	const char *lhs_op, *rhs_op;
	csvarinfo_t lhs, rhs;
	int size1 = 0;
	/******************/
	int total_no_of_iterations = 0;
	/******************/

	bool change;
	change = true;
	while (change) {
		// Vini, June'15
#if PT_TEST
		generate_call_return_constraints (obj_allptinfo);
		//size1=obj_allptinfo.map_size();

		//fprintf (dump_file, "\nLoop till unchanged");
#endif
		change = false;
		/***********/
		total_no_of_iterations++;
		/***********/

		for (int i = 0; i < VEC_length(constraint_t, aliases); i++) {
			con = VEC_index(constraint_t, aliases, i);
			if (con->rhs.ptr_arith && !con->heap_alloc) {
				fprintf(dump_file, "\n WARNING : Points to an undefined pointer \n ");
				con->rhs.var = undef_id;
				con->rhs.type = 0;
			}
			//fprintf(dump_file,"Processing constraint no.: %d \n",i);
			lhs_type = con->lhs.type;
			rhs_type = con->rhs.type;
			lhs_var_id = con->lhs.var;
			rhs_var_id = con->rhs.var;
#if PT_TEST			 
			if (lhs_type == 2 && rhs_type == 2)
			{
				fprintf (dump_file, "*lhs=*rhs");
				print_assignment_data (i);
			}
#endif
			bool temp = obj_allptinfo.Process_Input(lhs_var_id, lhs_type, rhs_var_id, rhs_type);
#if PT_TEST
			fprintf(dump_file,"lhs type = %d rhs type\t%d\n",lhs_type,rhs_type);
			fprintf(dump_file,"size = %d\t%d\t %d \t %d\n",change,temp,obj_allptinfo.map_size(),VEC_length (constraint_t, aliases));
#endif
			change = change || temp;

		}
#if PT_TEST
		//fprintf(dump_file,"change:%d\n",change);
		//fprintf(dump_file,"Printing map");
		//obj_allptinfo.Display_Map(1);
#endif
	}
}

Allptsinfo execute_ipacs(void) {
	Allptsinfo obj_allptinfo;
	if (!in_lto_p) {
		cerr << "in_lto_p is NOT set." << endl;
		return Allptsinfo();
		//return 0;
	}
	cerr << "in_lto_p IS set." << endl;
	//dump_file = stdout;

	struct function *old_cfun = cfun;
	tree old_cfundecl = current_function_decl;
	init_fn_aux();
	initialization();

	preprocess_control_flow_graph();
	call_process_inputs(obj_allptinfo);
	fprintf(dump_file, "Printing map:");
	obj_allptinfo.Display_Map(1);
	fprintf(dump_file, "Done Printing map:");

	/*
	 obj_allptinfo.print_failed_constraints();
	 fprintf(dump_file, "\n\n");

	 delete_block_aux();

	 end_fn_aux();
	 */
	return obj_allptinfo;
}

//struct simple_ipa_opt_pass pass_ipacs =
//{
//  {
//    SIMPLE_IPA_PASS,
//    "func",                                /* name */
//    NULL,	                            /* gate */
//    execute_ipacs,		            /* execute */
//    NULL,                                   /* sub */
//    NULL,                                   /* next */
//    0,                                      /* static_pass_number */
//    TV_INTEGRATION,                         /* tv_id */
//    0,                                      /* properties_required */
//    0,                                      /* properties_provided */
//    0,                                      /* properties_destroyed */
//    0,                                      /* todo_flags_start */
//    0                                       /* todo_flags_finish */
//  }
//};
//struct register_pass_info pass_info =
//{
//	&(pass_ipacs.pass),
//	"pta",
//	0,
//	PASS_POS_INSERT_AFTER
//};
//
//int plugin_init(struct plugin_name_args *plugin_info, struct plugin_gcc_version *version)
//{
//	register_callback(
//		plugin_info->base_name,
//		PLUGIN_PASS_MANAGER_SETUP,
//		NULL,
//		&pass_info);
//	return 0;
//}

