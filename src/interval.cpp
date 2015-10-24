#include "interval.hpp"
#include "parser.hpp"
unsigned int interval_count;
unsigned int reduce_graph_count = 0;

map< unsigned int, interval > interval_map;

unsigned int interval::get_id()
{
	return id;
}

void interval::set_id(unsigned int i)
{
	id = i;
}

unsigned int interval::get_header()
{
	return header;	
}

void interval::set_header(unsigned int h)
{
	header = h;
}

list< unsigned int > interval::get_node_list()
{
	return node_list;
}

void interval::set_node_list(list< unsigned int > sc)
{
	node_list = sc;
}

unsigned int interval::get_pred_count()
{
	return pred_count;
}

void interval::set_pred_count(unsigned int c)
{
	pred_count = c;
}

unsigned int interval::get_reach()
{
	return reach;
}

void interval::set_reach(unsigned int r)
{
	reach = r;
}

unsigned int interval::get_inter_order()
{
	return inter_order;
}

void interval::set_inter_order(unsigned int c)
{
	inter_order = c;
}

bool interval::is_marked()
{
	return marked;
}

void interval::set_marked()
{
	marked = true;
}

void interval::reset_marked()
{
	marked = false;
}

/*
bool operator<(const il & i1, const il & i2)
{
        if(i1.deref_list < i2.deref_list)
                return true;

        return false;
}
*/

bool operator==(const interval & i1, const interval & i2)
{
        if(i1.node_list == i2.node_list)
                return true;

        return false;

}

void interval::print_interval()
{
	fprintf(dump_file,"\nInterval Id: %d\n Nodes in the Interval\n", get_id());

	list< unsigned int >::iterator it;
	list< unsigned int > nodes = get_node_list();

	for(it = nodes.begin(); it != nodes.end(); it++)
	{
		fprintf(dump_file,"%d\t",*it);
	}

	fprintf(dump_file,"\nHeader of the Interval %d\n", get_header());
	fprintf(dump_file,"\nPred Count  %d\n", get_pred_count());
	fprintf(dump_file,"\nSize of Interval %d\n", nodes.size());

	if(is_marked())
		fprintf(dump_file,"\nInterval is Processed\n");
}

list< struct cgraph_node * > interval::get_cnodes()
{
//	fprintf(dump_file,"\nInside get_cnodes %d\n", get_id());
		
	list< unsigned int > nodes = get_node_list();
	list< struct cgraph_node * > result, temp;
	struct cgraph_node *cnode;

	list< unsigned int >::iterator it;
	interval I;

	for(it = nodes.begin(); it != nodes.end(); it++)
	{
		if(*it > func_num)
		{
			I = interval_map[*it];

			temp = I.get_cnodes();

			result.insert(result.end(), temp.begin(), temp.end());
		}
		else
		{
			cnode = func_numbering[*it];

			result.push_back(cnode);
		}	
	}

	list<struct cgraph_node * >::iterator lit;
//	fprintf(dump_file,"\nResult\n");

//	for(lit = result.begin(); lit != result.end(); lit++)
	{
//		fprintf(dump_file,"%s\t",cgraph_node_name(*lit));
	}

//	fprintf(dump_file,"\n");

	return result;
}

bool interval::is_equal(interval I)
{
	list< unsigned int > nodes1, nodes2;

	nodes1 = get_node_list();
	nodes2 = I.get_node_list();

	if(nodes1.size() != nodes2.size())
	{
		return false;
	}

	list< struct cgraph_node * > cnodes1, cnodes2;

	cnodes1 = get_cnodes();

	cnodes2 = I.get_cnodes();

	list< struct cgraph_node * >::iterator cit1, cit2;

	if(cnodes1.size() != cnodes2.size())
	{
		return false;
	}

	struct cgraph_node *c1, *c2;

	for(cit1 = cnodes1.begin(), cit2 = cnodes2.begin(); cit1 != cnodes1.end(); cit1++, cit2++)
	{
		c1 = *cit1;
		c2 = *cit2;

//		if(c1->uid != c2->uid)
		if(((function_info *)(c1->aux))->func_num != ((function_info *)(c2->aux))->func_num)
		{
			return false;
		}
	}
		
	return true;
}

unsigned int interval_graph::get_start_node()
{
	return start_node;
}

void interval_graph::set_start_node(unsigned int s)
{
	start_node = s;
}

graph_type interval_graph::get_edge_list()
{
	return edge_list;
}

void interval_graph::set_edge_list(graph_type g)
{
	edge_list = g;
}

set< unsigned int > interval_graph::get_interval_set()
{
	return interval_set;
}

void interval_graph::set_interval_set(set< unsigned int > s)
{
	interval_set = s;
}

list< unsigned int > interval_graph::search_node(unsigned int x)
{
	list<unsigned int> nodes;

	list< unsigned int > result; // = -1;

	graph_type edges  = get_edge_list();
	set< unsigned int > intervals = get_interval_set();
	set< unsigned int >::iterator sit;
	interval I;

	for(sit = intervals.begin(); sit != intervals.end(); sit++)
	{
		I = interval_map[*sit];

		nodes = I.get_node_list();

		if(find(nodes.begin(), nodes.end(), x) != nodes.end())
		{
			result.push_back(I.get_id());
//			return I.get_id();
		}
	}

	return result;
}

list< unsigned int > visited_d;
list< unsigned int > visit_d;

void interval_graph::top_sort_ordering()
{
	unsigned int s = visited_d.front();
	visited_d.pop_front();

//	fprintf(dump_file,"\nInside top_sort_ordering %d\n", s);

	struct cgraph_node *cnode;

	graph_type edges = get_edge_list();

	graph_type::iterator git;

	interval I = interval_map[s];
	interval J;

	visit_d.push_back(s);

	list< struct cgraph_node * > result;
	result = I.get_cnodes();

	list< struct cgraph_node * >::iterator lit;

	for(lit = result.begin(); lit != result.end(); lit++)
	{
		cnode = *lit;

//		fprintf(dump_file,"%s\t",cgraph_node_name(cnode));
//		fprintf(dump_file,"\nFunction Ordered in the Worklist %s\n", cgraph_node_name(cnode));

		index_func_array_d[func_count_d] = ((function_info *)(cnode->aux))->func_num;
		func_index_array_d[((function_info *)(cnode->aux))->func_num] = func_count_d;
		function_worklist_d[func_count_d] = true;
		preprocess_worklist[func_count_d] = true;
		func_count_d++;
	}	

	for(git = edges.begin(); git != edges.end(); git++)
	{
		if(get<0>(*git) == s)
		{

			if(find(visit_d.begin(), visit_d.end(), get<1>(*git)) == visit_d.end())
			{
				visited_d.push_back(get<1>(*git));
			}

		}
	}
}

void interval_graph::depth_ordering(unsigned int s)
{
//	fprintf(dump_file,"\nInside depth_ordering %d\n", s);

	struct cgraph_node *cnode;

	graph_type edges = get_edge_list();

	graph_type::iterator git;

	interval I = interval_map[s];
	interval J;
	I.reset_marked();
	interval_map[I.get_id()] = I;	

	for(git = edges.begin(); git != edges.end(); git++)
	{
		if(get<0>(*git) == s)
		{
			J = interval_map[get<1>(*git)];

			if(J.is_marked())
			{
				depth_ordering(get<1>(*git));
			}
		}
	}

	I = interval_map[s];

	list< struct cgraph_node * > result;
	result = I.get_cnodes();

	list< struct cgraph_node * >::reverse_iterator lit;

	for(lit = result.rbegin(); lit != result.rend(); lit++)
	{
		cnode = *lit;

//		fprintf(dump_file,"%s\t",cgraph_node_name(cnode));
//		fprintf(dump_file,"\nFunction Ordered in the Worklist %s %d\n", cgraph_node_name(cnode), func_count);

		index_func_array[func_count] = ((function_info *)(cnode->aux))->func_num;
		func_index_array[((function_info *)(cnode->aux))->func_num] = func_count;
		function_worklist[func_count] = true;
		func_count++;

	}	
}

void interval_graph::set_order_of_worklist_d()
{
	set< unsigned int > intervals = get_interval_set();
	graph_type edges = get_edge_list();

	graph_type::iterator git;

	interval I;
	list< struct cgraph_node * > temp, result;

	struct cgraph_node *cnode;
	list< struct cgraph_node * >::iterator rlit;

	set< unsigned int >::iterator sit;

//	fprintf(dump_file,"\nfunc_count_d = %d\n",func_count_d);

	if(intervals.size() == 1 && edges.size() == 0)
	{
		sit = intervals.begin();

		I = interval_map[*sit];

		result = I.get_cnodes();

//		fprintf(dump_file,"\nOrder of Functions to be processed\n");

		for(rlit = result.begin(); rlit != result.end(); rlit++)
		{
			cnode = *rlit;

//			fprintf(dump_file,"%s\t", cgraph_node_name(cnode));
//			fprintf(dump_file,"\nFunction Ordered in the Worklist %s %d %d\n", cgraph_node_name(cnode), ((function_info *)(cnode->aux))->func_num, func_count_d);

			index_func_array_d[func_count_d] = ((function_info *)(cnode->aux))->func_num;
			func_index_array_d[((function_info *)(cnode->aux))->func_num] = func_count_d;
//			fprintf(dump_file,"\nFunction Ordered in the Worklist %s %d %d %d\n", cgraph_node_name(cnode), index_func_array_d[func_count_d], func_index_array_d[((function_info *)(cnode->aux))->func_num], func_count_d);
			function_worklist_d[func_count_d] = true;
			preprocess_worklist[func_count_d] = true;
			func_count_d++;

		}

//		fprintf(dump_file,"\n Func Count in Ordering Worklist %d\n",func_count_d);
		return;
	}

//	fprintf(dump_file,"\nOrder of Functions to be processed\n");
	
	visited_d.clear();
	visit_d.clear();

	visited_d.push_back(get_start_node());
//	visit_d.push_back(get_start_node());

	while(!visited_d.empty())
	{
		top_sort_ordering();
	}
}

void interval_graph::set_order_of_worklist()
{
//	fprintf(dump_file,"\nFinal Interval Graph\n");
//	print_interval_graph();

	set< unsigned int > intervals = get_interval_set();
	graph_type edges = get_edge_list();

	graph_type::iterator git;

	interval I;
	list< struct cgraph_node * > temp, result;

	struct cgraph_node *cnode;
	list< struct cgraph_node * >::reverse_iterator lit;
	list< struct cgraph_node * >::iterator rlit;

	set< unsigned int >::iterator sit;

	if(intervals.size() == 1 && edges.size() == 0)
	{
		sit = intervals.begin();

		I = interval_map[*sit];

		result = I.get_cnodes();

//		fprintf(dump_file,"\nOrder of Functions to be processed\n");

		for(lit = result.rbegin(); lit != result.rend(); lit++)
		{
			cnode = *lit;

//			fprintf(dump_file,"%s\t", cgraph_node_name(cnode));
//			fprintf(dump_file,"\nFunction Ordered in the Worklist %s %d\n", cgraph_node_name(cnode), func_count);

			index_func_array[func_count] = ((function_info *)(cnode->aux))->func_num;
			func_index_array[((function_info *)(cnode->aux))->func_num] = func_count;
			function_worklist[func_count] = true;
			func_count++;

		}

//		fprintf(dump_file,"\n Func Count in Ordering Worklist %d\n",func_count);
		return;
	}

//	fprintf(dump_file,"\nOrder of Functions to be processed\n");

	depth_ordering(get_start_node());

	#if 0
	set< unsigned int > total_cnodes;
	unsigned int x, y;
	list< unsigned int > interval_order;

	struct cgraph_node *c;

	for(git = edges.begin(); git != edges.end(); git++)
	{
		x = get<0>(*git);
		y = get<1>(*git);

		if(total_cnodes.find(x) == total_cnodes.end())
		{
			total_cnodes.insert(x);

			I = interval_map[x];

			temp = I.get_cnodes();

			for(rlit = temp.begin(); rlit != temp.end(); rlit++)
			{
				c = *rlit;

				interval_order.push_back(((function_info *)(c->aux))->func_num);
			}
		}		
		if(total_cnodes.find(y) == total_cnodes.end())
		{
			total_cnodes.insert(y);

			I = interval_map[y];

			temp = I.get_cnodes();

			for(rlit = temp.begin(); rlit != temp.end(); rlit++)
			{
				c = *rlit;

				interval_order.push_back(((function_info *)(c->aux))->func_num);
			}
		}		
	}

	list< unsigned int >::reverse_iterator order_it;

	for(order_it = interval_order.rbegin(); order_it != interval_order.rend(); order_it++)
	{
		index_func_array[func_count] = *order_it;
		func_index_array[*order_it] = func_count;
		function_worklist[func_count] = true;
		func_count++;
	}
	#endif

	#if 0
	for(git = edges.begin(); git != edges.end(); git++)
	{
		I = interval_map[get<0>(*git)];

		temp = I.get_cnodes();

		result.insert(result.end(), temp.begin(), temp.end());
		
		I =  interval_map[get<1>(*git)];

		temp = I.get_cnodes();

		result.insert(result.end(), temp.begin(), temp.end());
	}

	for(lit = result.begin(); lit != result.end(); lit++)
	{
		cnode = *lit;

		fprintf(dump_file,"%s\t", cgraph_node_name(cnode));
	}
	#endif

//	fprintf(dump_file,"\n");
//	fprintf(dump_file,"\n Func Count in Ordering Worklist %d\n",func_count);

//	print_interval_graph();
}

void interval_graph::create_edges_first_phase(interval I)
{
	set< unsigned int > intervals = get_interval_set();

	list< unsigned int > nodes1 = I.get_node_list();

	set< unsigned int >:: iterator sit;
	list< unsigned int >::iterator lit;

	struct cgraph_node *cnodex, *cnodey;
	struct cgraph_edge *edge;

	unsigned int x, y;
	unsigned int id1 = I.get_id();
	unsigned int id2;
	interval J;
	list< unsigned int > result, nodes2;
	graph_type edges = get_edge_list();
	tuple< unsigned int, unsigned int > t;
	list< unsigned int > tmp;

	unsigned int head1, head2;

	head1 = I.get_header();

//	for(lit = nodes1.begin(); lit != nodes1.end(); lit++)
	{
//		cnodex = func_numbering[*lit];
		cnodex = func_numbering[head1];

		for(edge = cnodex->callers; edge; edge = edge->next_caller)
		{
			cnodey = edge->caller;

			if (!gimple_has_body_p (cnodey->decl) || cnodey->clone_of)
				continue;

			y = ((function_info *)(cnodey->aux))->func_num;

			tmp = search_node(y);

//			if(tmp != -1)
			{
				result.insert(result.end(), tmp.begin(), tmp.end());
			}
		}	
	}

	for(lit = result.begin(); lit != result.end(); lit++)
	{
		t = make_tuple(*lit, id1);

		edges.push_back(t);
	}

	I.set_pred_count(I.get_pred_count() + result.size());
	interval_map[id1] = I;

	result.clear();

	for(sit = intervals.begin(); sit != intervals.end(); sit++)
	{
		list< unsigned int > temp;

		J = interval_map[*sit];

		head2 = J.get_header();
		nodes2 = J.get_node_list();

//		for(lit = nodes2.begin(); lit != nodes2.end(); lit++)
		{
//			cnodex = func_numbering[*lit];
			cnodex = func_numbering[head2];

			for(edge = cnodex->callers; edge; edge = edge->next_caller)
			{
				cnodey = edge->caller;

				if (!gimple_has_body_p (cnodey->decl) || cnodey->clone_of)
					continue;
	
				y = ((function_info *)(cnodey->aux))->func_num;

				if(find(nodes1.begin(), nodes1.end(), y) != nodes1.end())
				{
					temp.push_back(J.get_id());
				}
			}
		}
		
		J.set_pred_count(J.get_pred_count() + temp.size());
		interval_map[J.get_id()] = J;

		result.insert(result.end(), temp.begin(), temp.end());	
	}

	for(lit = result.begin(); lit != result.end(); lit++)
	{
		t = make_tuple(id1, *lit);

		edges.push_back(t);
	}

	intervals.insert(id1);

	set_interval_set(intervals);
	set_edge_list(edges);

//	fprintf(dump_file,"\nKay Chalu\n");
//	print_interval_graph();

}

interval_graph interval_graph::create_edges(interval_graph g, interval I)
{
//	fprintf(dump_file,"\nInside create_edges()\n");

	set< unsigned int > intervals = g.get_interval_set();

	list< unsigned int > nodes1 = I.get_node_list();

	set< unsigned int >:: iterator sit;
	list< unsigned int >::iterator lit;

	unsigned int x, y;
	unsigned int id1 = I.get_id();
	unsigned int id2;
	interval J;

	list< unsigned int > result, nodes2;

	graph_type edges_old = get_edge_list();
	graph_type edges = g.get_edge_list();
	graph_type::iterator git;
	tuple< unsigned int, unsigned int > t;

	unsigned int head1, head2;
	list< unsigned int > tmp;

	head1 = I.get_header();

//	fprintf(dump_file,"\nHead1 %d\n",head1);
//	print_interval_graph();

//	for(lit = nodes1.begin(); lit != nodes1.end(); lit++)
	{
		for(git = edges_old.begin(); git != edges_old.end(); git++)
		{
			if(get<1>(*git) == head1)
//			if(get<1>(*git) == *lit)
			{
				y = get<0>(*git);

//				fprintf(dump_file,"\nY %d\n",y);

				tmp = g.search_node(y);

//				fprintf(dump_file,"\ntmp %d\n",tmp);
//				if(tmp != -1)
				{
					result.insert(result.end(), tmp.begin(), tmp.end());
				}
			}
		}	
	}

//	fprintf(dump_file,"\nRessult for Creating Edges\n");

	for(lit = result.begin(); lit != result.end(); lit++)
	{
//		fprintf(dump_file,"%d\t",*lit);
		t = make_tuple(*lit, id1);

		edges.push_back(t);
	}
	graph_type::iterator gi;

	
	for(gi = edges.begin(); gi != edges.end(); gi++)
	{
//		fprintf(dump_file,"\n%d -> %d\n", get<0>(*gi), get<1>(*gi));
	}

//	fprintf(dump_file,"\n");

	I.set_pred_count(I.get_pred_count() + result.size());
	interval_map[id1] = I;

	result.clear();

	for(sit = intervals.begin(); sit != intervals.end(); sit++)
	{
		list< unsigned int > temp;

		J = interval_map[*sit];

		head2 = J.get_header();
		nodes2 = J.get_node_list();

//		for(lit = nodes2.begin(); lit != nodes2.end(); lit++)
		{
			for(git = edges_old.begin(); git != edges_old.end(); git++)
			{
				if(get<1>(*git) == head2)
//				if(get<1>(*git) == *lit)
				{
					y = get<0>(*git);

					if(find(nodes1.begin(), nodes1.end(), y) != nodes1.end())
					{
						temp.push_back(J.get_id());
					}
				}
			}
		}
		
		J.set_pred_count(J.get_pred_count() + temp.size());
		interval_map[J.get_id()] = J;

		result.insert(result.end(), temp.begin(), temp.end());	
	}

	for(lit = result.begin(); lit != result.end(); lit++)
	{
		t = make_tuple(id1, *lit);

		edges.push_back(t);
	}

	intervals.insert(id1);

	g.set_interval_set(intervals);
	g.set_edge_list(edges);

//	fprintf(dump_file,"\nKay Chalu\n");
//	g.print_interval_graph();
	
	return g;	
}

void interval_graph::reduce_interval_graph()
{
//	fprintf(dump_file,"\nInside reduce_interval_graph\n");

	unsigned int s = get_start_node();

//	fprintf(dump_file,"\nStart Node %d\n",s);
	set< unsigned int > nodes = get_interval_set();
	graph_type edges = get_edge_list();

	list< unsigned int > H;

	interval_graph g;
	unsigned int i = 1;

//	fprintf(dump_file,"\nhiiiiiii\n");

	H.push_back(s);
	unsigned int x, y, h, z;
	unsigned int order;
	interval ix, iy;
	graph_type::iterator git;

	list< unsigned int >::iterator it;

	while(!H.empty())
	{
		h = H.front();
		H.pop_front();

		order = 0;

		interval I;
		I.set_id(interval_count++);
		I.set_header(h);
		I.set_pred_count(0);
		I.set_inter_order(0);

		list< unsigned int > Ih;

		Ih.push_back(h);
		ix = interval_map[h];

//		ix.print_interval();

		ix.set_inter_order(order++);

//		fprintf(dump_file,"\nHellooo\n");
//		fprintf(dump_file,"\nHeader %d\n",h);
		bool no_edges = false;

		for(it = Ih.begin(); it != Ih.end(); it++)
		{
			x = *it;

			ix = interval_map[x];

			if(ix.is_marked())
			{
//				fprintf(dump_file,"\nHeeee\n");
				no_edges = true;
				continue;
			}

//			fprintf(dump_file,"\nHiiii\n");
	
			ix.set_marked();
			interval_map[x] = ix;

			for(git = edges.begin(); git != edges.end(); git++)
			{
				z = get<0>(*git);

				if(z != x)
				{
					continue;
				}
				
				y = get<1>(*git);

				iy = interval_map[y];

				if(iy.get_pred_count() > 0)
					iy.set_pred_count(iy.get_pred_count() - 1);

				if(iy.get_reach() == 0)
				{
					iy.set_reach(I.get_id());

					if(iy.get_pred_count() == 0)
					{
						Ih.push_back(y);
	
						iy.set_inter_order(order++);
					}
					else
					{
						if(find(H.begin(), H.end(), y) == H.end())
						{
							H.push_back(y);
						}
					}
				}
				else if(iy.get_reach() == I.get_id() && iy.get_pred_count() == 0)
				{
					Ih.push_back(y);

					H.remove(y);
				}
			}
		}

		if(!no_edges)
		{
			
		I.set_node_list(Ih);
		I.set_reach(0);
		I.reset_marked();	

		set< unsigned int > nodes1 = g.get_interval_set();
		graph_type edges1 = g.get_edge_list();
		unsigned int id = I.get_id();
		tuple< unsigned int, unsigned int > t;
	
		if(i == 1)
		{
			i++;
			g.set_start_node(id);

			nodes1.insert(id);

			interval_map[id] = I;
			g.set_interval_set(nodes1);
		}
		else
		{
			g = create_edges(g, I);
//			g.print_interval_graph();
		}

//		fprintf(dump_file,"\nNewly Created Interval in Reduced Graph\n");
		I = interval_map[id];
//		I.print_interval();
//		fprintf(dump_file,"\nIthe\n");
		}
	}


	#if 1
	if(get_interval_set().size() == g.get_interval_set().size() || (g.get_interval_set().size() == 1 && g.get_edge_list().size() == 0))
//	if(is_equal(g) || (g.get_interval_set().size() == 1 && g.get_edge_list().size() == 0))
	{
		reduce_graph_count++;
//		fprintf(dump_file,"\nReduced Interval Graph No %d Original Node Count %d Node Count %d\n", reduce_graph_count, get_interval_set().size(), g.get_interval_set().size());

		set< unsigned int >::iterator interval_it;

		for(interval_it = g.get_interval_set().begin(); interval_it != g.get_interval_set().end(); interval_it++)
		{
//			fprintf(dump_file,"\nInterval %d Number of Nodes %d\n",*interval_it, interval_map[*interval_it].get_node_list().size());
		}

//		fprintf(dump_file,"\nBase Condition for Graph Reducibility\n");

//		g.print_interval_graph();

		set_order_of_worklist_d();
		set_order_of_worklist();

		#if STATS
		fprintf(dump_file,"\nGraph Reduction Process Terminates\n");
		fprintf(dump_file,"\nFinal Interval Graph\n");
		print_interval_graph();
		fprintf(dump_file,"\nNumber of Steps Required for Interval Analysis = %d\n", reduce_graph_count);
		#endif
	}
	else
	{
//		fprintf(dump_file,"\nRecursive Call\n");
		reduce_graph_count++;
//		fprintf(dump_file,"\nReduced Interval Graph No %d Original Node Count %d Node Count %d\n", reduce_graph_count, get_interval_set().size(), g.get_interval_set().size());

		set< unsigned int >::iterator interval_it;

		for(interval_it = g.get_interval_set().begin(); interval_it != g.get_interval_set().end(); interval_it++)
		{
//			fprintf(dump_file,"\nInterval %d Number of Nodes %d\n",*interval_it, interval_map[*interval_it].get_node_list().size());
		}

//		g.print_interval_graph();
		g.reduce_interval_graph();	
//		g.set_order_of_worklist();
	}
	#endif

}

bool interval_graph::is_equal(interval_graph g)
{
	set< unsigned int > nodes1, nodes2;
		
//	fprintf(dump_file,"\nInside is_equal\n");

	graph_type edges1, edges2;

	nodes1 = get_interval_set();
	nodes2 = g.get_interval_set();

	edges1 = get_edge_list();
	edges2 = g.get_edge_list();

	set< unsigned int >::iterator sit1, sit2;
	graph_type::iterator git1, git2;

	if(nodes1.size() != nodes2.size())
	{
		return false;
	}	
	else if(edges1.size() != edges2.size())
	{
		return false;
	}

	interval I, J, K, L;
	int i = 0;

	for(sit1 = nodes1.begin(); sit1 != nodes1.end(); sit1++)
	{
		I = interval_map[*sit1];
//		I.print_interval();

		for(sit2 = nodes2.begin(); sit2 != nodes2.end(); sit2++)
		{
			J = interval_map[*sit2];

//			J.print_interval();

			if(I.is_equal(J))
			{
//				fprintf(dump_file,"\nIntervals Equal\n");
				i++;
				break;
			}
		}
	}
//	fprintf(dump_file,"\nI %d\n",i);
//	fprintf(dump_file,"\nNode Size %d\n",nodes1.size());

	if( i != nodes1.size())
	{
		return false;
	}

	i = 0;

	for(git1 = edges1.begin(); git1 != edges1.end(); git1++)
	{
		I = interval_map[get<0>(*git1)];
		J = interval_map[get<1>(*git1)];

		for(git2 = edges2.begin(); git2 != edges2.end(); git2++)
		{
			K = interval_map[get<0>(*git2)];
			L = interval_map[get<1>(*git2)];

			if(I.is_equal(K) && J.is_equal(L))
			{
				i++;
				break;
			}
		}
	}

	if( i != edges1.size())
	{
		return false;
	}

	return true;

}

/*
bool operator<(const il & i1, const il & i2)
{
        if(i1.deref_list < i2.deref_list)
                return true;

        return false;
}
*/

bool operator==(const interval_graph & g1, const interval_graph & g2)
{
	graph_type::iterator it1, it2;
	interval il1, il2, ir1, ir2;
	bool match;
	graph_type edges1, edges2;

	edges1 = g1.edge_list;
	edges2 = g2.edge_list;

        if(g1.interval_set == g2.interval_set)
	{
		if(edges1.size() == edges2.size())
		{
			for(it1 = edges1.begin(); it1 != edges1.end(); it1++)
			{
				il1 = interval_map[get<0>(*it1)];
				ir1 = interval_map[get<1>(*it1)];

				match = false;

				for(it2 = edges2.begin(); it2 != edges2.end(); it2++)
				{
					il2 = interval_map[get<0>(*it2)];
					ir2 = interval_map[get<1>(*it2)];

					if(il1 == il2 && ir1 == ir2)
					{
						match = true;
						break;
					}
				}

				if(!match)
				{
					return false;
				}
			}
			return true;
		}
	}

        return false;

}

void interval_graph::print_interval_graph()
{
	set< unsigned int > intervals = get_interval_set();
	graph_type edges = get_edge_list();

	list< unsigned int > nodes;

	list< unsigned int >:: iterator lit;
	graph_type::iterator it;
	set< unsigned int >::iterator sit;
	interval i;

	fprintf(dump_file,"\nNumber of Intervals in the Graph %d\n", intervals.size());
	fprintf(dump_file,"\nIntervals in the Graph\n");
	
	for(sit = intervals.begin(); sit != intervals.end(); sit++)
	{
		i = interval_map[*sit];
		i.print_interval();
	}

	fprintf(dump_file,"\nEdges between the Intervals in the Graph\n");

	for(it = edges.begin(); it != edges.end(); it++)
	{
		fprintf(dump_file,"\n%d -> %d\n", get<0>(*it), get<1>(*it));
	}
}

void find_interval_first_phase(unsigned int s)
{
//	fprintf(dump_file,"\nInside find_interval_first_phase\n");

	list< unsigned int > H, Ih;

	interval_count = func_num + 1; 

	H.push_back(s);

	struct cgraph_node *cnodex, *cnodey;

	unsigned int x, y, h;

	unsigned int order;
	struct cgraph_edge *edge;
	list< unsigned int >::iterator it;

	interval_graph g;
	unsigned int i = 1;
//	fprintf(dump_file,"\nInterval Count %d\n", interval_count);

	while(!H.empty())
	{
		h = H.front();
		H.pop_front();
		
		interval I;
		I.set_id(interval_count);
		interval_count++;
		I.set_pred_count(0);
		I.set_inter_order(0);

		list< unsigned int > Ih;

		Ih.push_back(h);
		I.set_header(h);
		order = 0;
		
		cnodex = func_numbering[h];

		((function_info *)(cnodex->aux))->set_inter_order(order++);

//		fprintf(dump_file,"\nHeader %s %d\n", cgraph_node_name(cnodex), h);

		for(it = Ih.begin(); it != Ih.end(); it++)
		{
			x = *it;

			cnodex = func_numbering[x];

//			fprintf(dump_file,"\nCaller %s %d\n", cgraph_node_name(cnodex), x);

			if(((function_info *)(cnodex->aux))->is_marked())
			{
				continue;
			}
			
			((function_info *)(cnodex->aux))->set_marked();

			for(edge = cnodex->callees; edge; edge = edge->next_callee)
			{
				cnodey = edge->callee;

				if (!gimple_has_body_p (cnodey->decl) || cnodey->clone_of)
					continue;

				y = ((function_info *)(cnodey->aux))->func_num;

//				fprintf(dump_file,"\nCallee %s %d Count %d\n", cgraph_node_name(cnodey), y, ((function_info *)(cnodey->aux))->get_pred_count());

				((function_info *)(cnodey->aux))->set_pred_count(((function_info *)(cnodey->aux))->get_pred_count() - 1);

//				fprintf(dump_file,"\nHiiiii\n");
//				fprintf(dump_file,"\nReach %d ID %d\n",((function_info *)(cnodey->aux))->get_reach(), I.get_id());

				if(((function_info *)(cnodey->aux))->get_reach() == 0)
				{
					((function_info *)(cnodey->aux))->set_reach(I.get_id());

					if(((function_info *)(cnodey->aux))->get_pred_count() == 0)
					{
						Ih.push_back(y);

						((function_info *)(cnodey->aux))->set_inter_order(order++);
					}
					else
					{
						if(find(H.begin(), H.end(), y) == H.end())
						{
							H.push_back(y);
						}
					}
				}
				else if(((function_info *)(cnodey->aux))->get_reach() == I.get_id() && ((function_info *)(cnodey->aux))->get_pred_count() == 0)
				{
					Ih.push_back(y);
					((function_info *)(cnodey->aux))->set_inter_order(order++);
				
					H.remove(y);
				}	
				
			}
		}

		I.set_node_list(Ih);
		I.set_reach(0);
		I.reset_marked();
		set< unsigned int > nodes = g.get_interval_set();
		graph_type edges = g.get_edge_list();
		tuple< unsigned int, unsigned int > t;

		unsigned int id = I.get_id();
//		fprintf(dump_file,"\nTesting Interval ID %d\n",id);

		if(i == 1)
		{
			i++;

			I.set_pred_count(0);

			g.set_start_node(id);

			nodes.insert(id);
//			fprintf(dump_file,"\nTesting Interval ID %d\n",id);

			interval_map[I.get_id()] = I;
			g.set_interval_set(nodes);
		}
		else
		{
			g.create_edges_first_phase(I);

		}

//		fprintf(dump_file,"\nNewly Created Interval\n");
		I = interval_map[id];
//		I.print_interval();	
//		interval_map[I.get_id()] = I;
	}

	set< unsigned int > intervals = g.get_interval_set();
	graph_type edges_of_graph = g.get_edge_list();

//	g.print_interval_graph();

	if(intervals.size() == 1 && edges_of_graph.size() == 0)
	{
//		fprintf(dump_file,"\nReducible Graph\n");
//		g.print_interval_graph();
		g.set_order_of_worklist_d();
		g.set_order_of_worklist();

		#if STATS
		fprintf(dump_file,"\nFinal Interval Graph\n");
		g.print_interval_graph();
		fprintf(dump_file,"\nNumber of Steps Required for Interval Analysis = 1\n");
		#endif
	}
	else
	{	
//		fprintf(dump_file,"\nFirst Phase Intervals Created\n");	
//		g.print_interval_graph();
		reduce_graph_count++;
//		fprintf(dump_file,"\nReduced Interval Graph No %d Original Node Count %d Node Count %d\n", reduce_graph_count, func_num + 1, intervals.size());
		set< unsigned int >::iterator interval_it;

//		for(interval_it = intervals.begin(); interval_it != intervals.end(); interval_it++)
		{
//			fprintf(dump_file,"\nInterval %d Number of Nodes %d\n",*interval_it, interval_map[*interval_it].get_node_list().size());
		}

		g.reduce_interval_graph();
//		g.set_order_of_worklist();
	}
}

void print_edges(graph_type edges)
{
	graph_type::iterator it;

	fprintf(dump_file,"\nEdges of a Graph\n");
	
	for(it = edges.begin(); it != edges.end(); it++)
	{
		fprintf(dump_file,"\n%d -> %d\n", get<0>(*it), get<1>(*it));
	}

}

void print_nodes(set< unsigned int > intervals)
{
	set< unsigned int >::iterator sit;
	interval i;

	fprintf(dump_file,"\nNodes in a Graph\n");
	
	for(sit = intervals.begin(); sit != intervals.end(); sit++)
	{
		i = interval_map[*sit];
		i.print_interval();
	}
}

//void get_field_insensitive_pta_info(Allptinfo & obj_allptinfo)
