#include "cgraph_node.hpp"

using namespace std;

map< unsigned int, struct cgraph_node * > func_numbering;

DVG function_info::get_prev_dvg()
{
	return prev_dvg;
}

void function_info::set_prev_dvg(DVG g)
{
	prev_dvg = g;
}

bool function_info::is_visited()
{
	return visited;
}

void function_info::set_visited(bool b)
{
	visited = b;
}

bool function_info::is_dvisited()
{
	return dvisited;
}

void function_info::set_dvisited(bool b)
{
	dvisited = b;
}

unsigned int function_info::get_num_bb()
{
	return num_bb;
}

void function_info::set_num_bb(unsigned int n)
{
	num_bb = n;
}

unsigned int function_info::get_end_block_index()
{
	return num_bb;
}

void function_info::set_end_block_index(unsigned int n)
{
	num_bb = n;
}

bool function_info::has_ret_type()
{
	return has_ret;
}

void function_info::set_ret_type()
{
	has_ret = true;
}

void function_info::reset_ret_type()
{
	has_ret = false;
}

#if 0
bool * function_info::get_live_worklist()
{
	return live_worklist;
}

bool * function_info::get_points_worklist()
{
	return points_worklist;
}

void function_info::set_live_worklist(bool *l)
{
	live_worklist = l;
}

void function_info::set_points_worklist(bool *p)
{
	points_worklist = p;
}
#endif

bool function_info::is_empty_worklist(int x)
{
	int i;
	
	if(x == 1) // Check Liveness Worklist
	{
		for(i=0; i < num_bb; i++)
		{
			if(live_worklist[i])
			{
				return false;
			}
		}

		return true;
	}
	else if(x == 2) // Check Points-to Worklist
	{
		for(i=0; i < num_bb; i++)
		{
			if(points_worklist[i])
			{
				return false;
			}
		}

		return true;

	}			
}

#if 0
int * function_info::get_rev_post_order()
{
	return rev_post_order;
}

int * function_info::get_bb_order()
{
	return bb_order;
}

void function_info::set_rev_post_order(int * rp)
{
	rev_post_order = rp;
}

void function_info::set_bb_order(int * b)
{
	bb_order = b;
}
#endif

map<unsigned int, set_edges> function_info::get_order_map()
{
	return order_map;
}

map<edge_id, unsigned int> function_info::get_rev_order_map()
{
	return rev_order_map;
}

void function_info::set_order_map(map<unsigned int, set_edges> o)
{
	order_map = o;
}

void function_info::set_rev_order_map(map<edge_id, unsigned int> o)
{
	rev_order_map = o;
}

set_edges function_info::get_edges_order(unsigned int o)
{
	return order_map[o];
}

void function_info::set_edges_order(unsigned int o, set_edges s)
{
	order_map[o] = s;
}

unsigned int function_info::get_order_edge(edge_id i)
{
	return rev_order_map[i];
}

void function_info::set_order_edge(unsigned int o, edge_id i)
{
	rev_order_map[i] = o;
}

set<unsigned int> function_info::get_params()
{
	return params;
}

void function_info::set_params(set<unsigned int> pr)
{
	params = pr;
}

void function_info::add_param(unsigned int x)
{
	set<unsigned int> temp;
	temp = get_params();
	temp.insert(x);
	set_params(temp);
}

unsigned int function_info::get_ret_id()
{
	return ret_id;
}

void function_info::set_ret_id(unsigned int rt)
{
	ret_id = rt;
}

DVG function_info::get_fi_dvg()
{
	return flow_insens;
}

void function_info::set_fi_dvg(DVG g)
{
	flow_insens = g;
}

unsigned int function_info::get_pred_count()
{
	return pred_count;
}

void function_info::set_pred_count(unsigned int c)
{
	pred_count = c;
}

unsigned int function_info::get_reach()
{
	return reach;
}

void function_info::set_reach(unsigned int r)
{
	reach = r;
}

unsigned int function_info::get_inter_order()
{
	return inter_order;
}

void function_info::set_inter_order(unsigned int c)
{
	inter_order = c;
}

bool function_info::is_marked()
{
	return marked;
}

void function_info::set_marked()
{
	marked = true;
}

void function_info::reset_marked()
{
	marked = false;
}
