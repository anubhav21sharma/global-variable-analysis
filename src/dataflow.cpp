#include"dataflow.hpp"
#include"cgraph_node.hpp"
#include"block_information.hpp"

using namespace std;

// For Statistics
        
unsigned int meet_count = 0;
unsigned int gcomp_count = 0;
unsigned int add_edge_count = 0;
unsigned int delete_edge_count = 0;
unsigned int infinity_edge_count = 0;
unsigned int constraint_edge_count = 0;

unsigned int edge_comp_count = 0;
unsigned int kill_count = 0;
unsigned int add_edges_func_count = 0;
unsigned int remove_edges_func_count = 0;
unsigned int func_comp_count = 0;

unsigned int ptr_arith_count_stack = 0;
unsigned int ptr_arith_count_heap = 0;

double edge_comp_time = 0;
double kill_time = 0;
double add_edges_time = 0;
double remove_edges_time = 0;
double meet_time = 0;
double func_comp_time = 0;

double temp_time;

map< struct cgraph_node *, set_cnodes > map_scc;

struct timeval t_start, t_end, result;

clock_t start, end;

void starttime() 
{ 
	#if 0
	gettimeofday(&t_start, NULL); 
	fprintf(dump_file,"\nInside starttime result %6ld \n",t_start.tv_sec);
	#endif

	start = clock();

//	fprintf(dump_file,"Starting of the program, start_t = %ld\n", start);
}

double stoptime() 
{ 
	#if 0
	unsigned long temp_time;

	gettimeofday (&t_end, NULL); 
	fprintf(dump_file,"\nInside endtime result %6ld \n",t_end.tv_sec);
//	timersub (&t_end, &t_start, &result); 
	temp_time = (t_end.tv_sec * 1000000 + t_end.tv_usec) - (t_start.tv_sec * 1000000 + t_start.tv_usec);
	fprintf(dump_file,"\nInside result %6ld \n",temp_time);
	fprintf(dump_file,"\nInside result %6ld \n",result.tv_sec);

	return temp_time;
	#endif

//	fprintf(dump_file,"\nInside stoptime result %6ld \n",temp_time);

	end = clock();

//	fprintf(dump_file,"End of the program, end = %ld\n", end);
	double elapsed_time = ((end-start)/(double)CLOCKS_PER_SEC)  * 1000;
	return elapsed_time;
} 

/*-----------------------------------------*/

unsigned int max_size;

unsigned int infi_thresh = 2;
unsigned int f_insens_thresh = 1;

int new_field = FSDEREF - 1;

set_nodes nodes_visited;
set_nodes may_info_lhs;
set_nodes may_info_rhs;

Node undef_node;

map< unsigned int, sec_map > node_map;

// IL APIs

il_type il::get_deref_list()
{
	return deref_list;
}

void il::set_deref_list(il_type i)
{
	deref_list = i;
}

void il::add_deref(int deref)
{
//	fprintf(dump_file,"\nInside add_deref\n");

//	fprintf(dump_file,"\nDeref %d\n",deref);

	il_type temp = get_deref_list();

	if(temp.size() >= 1 && deref != NDEREF)
	{
		if(temp.size() < f_insens_thresh)
		{
			#if TRACE
//			fprintf(dump_file,"\nField Senstivity\n");
			#endif

			temp.push_back(deref);
		}	
		else if(temp.size() < infi_thresh)
		{
			#if TRACE
//			fprintf(dump_file,"\nField Insensitive But no Infinity Edge\n");
			#endif

//			temp.push_back(NDEREF);
			temp.push_back(FSDEREF);
		}
		else
		{
			#if TRACE
//			fprintf(dump_file,"\nInfinity Edge\n");
			#endif

			set_infinity();

			#if STATS
			infinity_edge_count++;

//			fprintf(dump_file,"\nInfinity Edges Added so far %d\n",infinity_edge_count);
			#endif
		}
	}
	else
	{
//		fprintf(dump_file,"\nStack Variable\n");
//		fprintf(dump_file,"\nDeref %d\n",deref);
		temp.push_back(deref);
	}

	set_deref_list(temp);
}

il il::pop_deref_list()
{
	il_type temp = get_deref_list();

	int x = temp.front();

	temp.erase(temp.begin());

	set_deref_list(temp);

	return *this;	
}

int il::first_ele_deref_list()
{
	il_type temp = get_deref_list();

	return temp.front();
}

bool il::is_infinity()
{
	return infi;
}

void il::set_infinity()
{
	infi = true;
}

void il::print_il()
{
	il_type temp = get_deref_list();

	il_it it;

//	fprintf(dump_file,"\nIndirection List\n");

	for(it = temp.begin(); it != temp.end(); it++)
	{
		fprintf(dump_file,"%d\t",*it);
	}

	fprintf(dump_file,"\n");	

	if(is_infinity())
	{
		fprintf(dump_file,"\nInfinity Edge\n");
	}
}

il il::append(il il2) // il1.append(il2) => il1 ++ il2
{
	il il1, il3;

//	fprintf(dump_file,"\nInside append\n");

	il1 = *this;
	
	if(il2.length() == 0)
	{
		return il1;
	}

//	fprintf(dump_file,"\nILS\n");
//	il1.print_il();
//	il2.print_il();

	il_type temp = il2.get_deref_list();

	il_it it;

	il3 = il1;

	for(it = temp.begin(); it != temp.end(); it++)
	{
		il3.add_deref(*it);
	}

	return il3;
}

bool il::is_prefix(il il2) // il1.is_prefix(il2) => il1 <= il2
{
	il il1;

	il_type temp1, temp2;

	il1 = *this;

	temp1 = il1.get_deref_list();
	temp2 = il2.get_deref_list();

//	fprintf(dump_file,"\nInside is_prefix\n");
//	il1.print_il();	
//	il2.print_il();	

	if(il1.get_deref_list().size() > il2.get_deref_list().size())
	{
		return false;
	}
	#if 0
	else if(il1.length() == INFINITY && il2.length() == INFINITY)
	{
		return false;
	}
	#endif

	il_it it1, it2;
	int x;

	for(it1 = temp1.begin(), it2 = temp2.begin(); it1 != temp1.end(); it1++, it2++)
	{
		#if 0
		if(it2 == temp2.end() && il2.is_infinity())
		{
			x = FSDEREF;
		}
		else
		{
			x = *it2;
			it2++;
		}
		#endif
		
		if((*it1 != *it2) && (*it1 != FSDEREF || *it2 != FSDEREF))
		{
//			fprintf(dump_file,"\nFalse\n");
			return false;
		}
	}

//	fprintf(dump_file,"\nTrue\n");
	return true;
}

bool il::is_eq(il il2)
{
	il il1 = *this;

	#if 0	
	if(il1.length() == INFINITY && il2.length() == INFINITY)
	{
		il_type temp1, temp2;

		temp1 = il1.get_deref_list();
		temp2 = il2.get_deref_list();

		il_it it1, it2;
		
		for(it1 = temp1.begin(), it2 = temp2.begin(); it1 != temp1.end(); it1++, it2++)
		{
			if(*it1 != *it2)
			{
				return false;	
			}
		}
		
		return true;
	}
	#endif

	return (il1.is_prefix(il2) && il2.is_prefix(il1));
}

il il::common_part(il il2)
{
	il il1, il3;

	il1 = *this;

	il_type temp1, temp2;

	temp1 = il1.get_deref_list();	
	temp2 = il2.get_deref_list();	

	il_it it1, it2;

	int x, y;

	for(it1 = temp1.begin(), it2 = temp2.begin(); it1 != temp1.end(); it1++, it2++)
	{

		#if 0
		if(it1 == temp1.end() && il1.is_infinity())
		{
			x = FSDEREF;
		}
		else
		{
			x = *it1;
			it1++;
		}

		if(it2 == temp2.end() && il2.is_infinity())
		{
			y = FSDEREF;
		}
		else
		{
			y = *it2;
			it2++;
		}
		#endif
		
		if((*it1 == FSDEREF) || *it2 == FSDEREF)
		{
			il3.add_deref(FSDEREF);	
		}
		else if(x == y)
		{
			il3.add_deref(x);
		}
		else
		{
			break;
		}
	}

	return il3;
}

il il::get_remainder(il il2) // il1.get_remainder(il2) => il1 = il2 ++ il3
{
//	fprintf(dump_file,"\nInside get_remainder\n");

	il il1, il3;

	il1 = *this;

	if(!il2.is_prefix(il1))
	{
//		fprintf(dump_file,"\nPrefix Not True\n");
		return il3;
	}	

	il_it it1, it2;

	il_type temp1, temp2;

	temp1 = il1.get_deref_list();
	temp2 = il2.get_deref_list();

	int x;

	#if 1
	for(it1 = temp1.begin(), it2 = temp2.begin(); it2 != temp2.end(); it1++, it2++)
	{
//		fprintf(dump_file,"\nHiiiiiiiiiii\n");
		#if 0
		if(it1 == temp1.end() && il1.is_infinity())
		{
			x = FSDEREF;
		}
		else
		{
			x = *it1;
			it1++;
		}
		#endif
		if((*it1 != *it2) && (*it1 != FSDEREF || *it2 != FSDEREF))
//		if((*it1 != *it2) || *it1 == FSDEREF)
		{
			return il3;
		}

//		fprintf(dump_file,"\nHelloooooooooooo\n");
	}

//	fprintf(dump_file,"\nHiiiiiiiiiii\n");

	for(it1; it1 != temp1.end(); it1++)
	{
//		fprintf(dump_file,"\n%d\n",*it1);
		il3.add_deref(*it1);
	}
	#endif

//	fprintf(dump_file,"\nHiiiiiiiiiii\n");

	#if 1
	il_type temp = il3.get_deref_list();

//	il_it it = il3.end();

	if(il3.is_infinity() && temp.size() < infi_thresh)
	{
		while(temp.size() < infi_thresh)
		{
			il3.add_deref(FSDEREF);
		}
	}
	#endif

	return il3;
}

unsigned int il::length()
{
	il_type temp = get_deref_list();

//	fprintf(dump_file,"\nhelloooo\n");

	if(is_infinity())
	{
		return INFINITY;
	}

	return temp.size();
}

bool operator<(const il & i1, const il & i2)
{
	if(i1.deref_list < i2.deref_list)
		return true;
	
	return false;
}

bool operator==(const il & i1, const il & i2)
{
	if(i1.deref_list == i2.deref_list)
		return true;
	
	return false;

}

// Node APIs

Node::Node(struct constraint_expr e, int cons_id)
{
	set_var_id(e.var);

//	fprintf(dump_file,"\nVar ID %d, Var name: %s, Var Offset: %d, Var Type: %d\n",e.var, get_var_name(e.var), e.offset, e.type);

	il ilt;

	if(e.type == 1)
	{
		ilt.add_deref(NDEREF);	
	}
	else if(e.type == 2)
	{
		ilt.add_deref(NDEREF);

//		fprintf(dump_file,"\nNode ID: %d, Node name: %s, Node Offset: %d\n",e.var, get_var_name(e.var), e.offset);

		if(!unexpandable_var(e.var, e.offset))
		{
//			fprintf(dump_file,"\nNode Constructor Indirection %d for variable %s\n",e.offset, get_var_name(e.var)); 
			ilt.add_deref(e.offset);
		}
		else
		{
//			fprintf(dump_file,"\nNode Constructor Indirection -1 for variable %s\n", get_var_name(e.var)); 
			ilt.add_deref(NDEREF);
		}
	}
	
	set_ind_list(ilt);

//	fprintf(dump_file,"\nIndirection List of Node\n");
//	ilt.print_il();

//	ilt.print_il();

	add_node_map();
}


unsigned int Node::get_var_id()
{
	return var_id;
} 

il Node::get_ind_list()
{
	return ind_list;
}

node_id Node::get_node_id()
{
	return nid;
}

void Node::set_var_id(unsigned int id)
{
	var_id = id;
}

void Node::set_ind_list(il il1)
{
	ind_list = il1;
}

void Node::set_node_id(node_id n)
{
	nid = n;
}

bool operator<(const Node & n1, const Node & n2)
{
	if(n1.nid < n2.nid)
		return true;
	
	return false;

}

bool operator==(const Node & n1, const Node & n2)
{
	if(n1.nid == n2.nid)
		return true;
	
	return false;
}

bool Node::sim(Node n2) // n1 \sim n2
{
//	fprintf(dump_file,"\nInside sim\n");

	if(get_var_id() == n2.get_var_id())
		if(get_ind_list().is_prefix(n2.get_ind_list()))
		{
			#if 0
			fprintf(dump_file,"\nTrue\n");
			get_ind_list().print_il();
			n2.get_ind_list().print_il();
			#endif

			return true;
		}

//	fprintf(dump_file,"\nFalse\n");
	return false;
}

bool Node::node_eq(Node n2) // n1 \equiv n2
{
	if(get_node_id() == n2.get_node_id())
		return true;

	return false;
}

Node Node::construct_new_node(edge_id eid, int type)
{
//	fprintf(dump_file,"\nInside construct_new_node\n");

	Edge e = get_edge(eid);
//	e.print_edge();

	Node new_node;
	
	new_node.set_var_id(e.get_rhs().get_var_id());

	il il1, il2, il3;

	il1 = e.get_rhs().get_ind_list();
	il2 = e.get_lhs().get_ind_list();
	il3 = get_ind_list();

	if(!il2.is_prefix(il3))
	{
		return *this;
	}

	il il4, il5;

	#if 0
	fprintf(dump_file,"\nIn construct new node\n");

	fprintf(dump_file,"\np - il\n");
	il3.print_il();

	fprintf(dump_file,"\nlhs - il\n");
	il2.print_il();

	fprintf(dump_file,"\nrhs - il\n");
	il1.print_il();

	il4 = il3.get_remainder(il2);

	fprintf(dump_file,"\nRemainder p/lhs\n");
	il4.print_il();

	il5 = il1.append(il4);	

	fprintf(dump_file,"\nAppend RHS ++ Remainder\n");
	il5.print_il();

	fprintf(dump_file,"\nDone\n");
	#endif


	il4 = il3.get_remainder(il2);

	il5 = il1.append(il4);	

	il il_nn = il5; // e.get_rhs().get_ind_list().append(get_ind_list().get_remainder(e.get_lhs().get_ind_list()));

//	fprintf(dump_file,"\nAfter processing\n");
//	il_nn.print_il();

	new_node.set_ind_list(il_nn);

	new_node.add_node_map();

//	fprintf(dump_file,"\nHelloooo\n");

	Node n = new_node.get_structure_node(type);

//	fprintf(dump_file,"\nHiiii\n");
	return n;	

//	return new_node;
}

void Node::add_node_map()
{
	Node n;
//	fprintf(dump_file,"\nInside add_node_map\n");
	
	unsigned int vid = get_var_id();

	node_id id;
	nodes_it nit;

	if(vid == undef_id)
	{
		id = undef_node.get_node_id();
		il il1;
//		il1.add_deref(NDEREF);
		set_ind_list(il1);	
		set_node_id(id);
	
		return;
	}
	else if(vid == nothing_id)
	{
		il il1;
		set_ind_list(il1);
		node_id tmp = make_tuple(1,0,0);
		set_node_id(tmp);
	}

	il ilt = get_ind_list();

	unsigned int size = ilt.length();

	vec_nodes temp = node_map[vid][size];
	int i;

	if(temp.empty())
	{
		id = make_tuple(vid, size, 0);
	
		set_node_id(id);

		temp.push_back(*this);

		node_map[vid][size] = temp;	

	}
	else
	{
		int m = -1;
		bool found = false;
		
		for(nit=temp.begin(); nit != temp.end(); nit++)
		{
			m++;

			n = *nit;
			
			if(n.get_ind_list().is_eq(ilt))
			{
				i = m; //temp.size();
				id = make_tuple(vid, size, i);

				set_node_id(id);

				found = true;

				break;
			}
		}

		if(!found)
		{
			i = temp.size();

			id = make_tuple(vid, size, i);

			set_node_id(id);

			temp.push_back(*this);

			node_map[vid][size] = temp;

		}
	}
}

Node Node::con_dep()
{
	if(CDV.find(get_var_id()) != CDV.end())
	{
		return *this;
	}	
	else
	{
		node_id id = make_tuple(get_var_id()+1,1,0);

		Node n = get_node(id);
		
		return n;
	}
}

void Node::print_node()
{
	int vid = get_var_id();
	il ilt = get_ind_list();

	const char *nn = "i";
        const char *name,*fname;

	fprintf(dump_file,"\nNode: %d => %s\n",vid, get_var_name(vid));
	ilt.print_il();
}

Node Node::get_structure_node(int type)
{
//	fprintf(dump_file,"\nInside get_structure_node\n");
	il il1 = get_ind_list();

	il_type temp = il1.get_deref_list();

	il_it it = temp.begin();
	unsigned int vid = get_var_id();

	if(it == temp.end())
	{
		return *this;
	}

	Node n;
	il ilt;	
	csvarinfo_t vi;
	int x;

	if(*it == NDEREF)
	{
		x = 0;
	}
	else
	{
		x = *it;
	}
		#if 0
		ilt.add_deref(new_field++);
		n.set_var_id(get_var_id());
		n.set_ind_list(ilt);

		n.add_node_map();

		return n;
		}
		#endif

	if(!unexpandable_var(vid,x))
	{
		if(*it == NDEREF || *it == FSDEREF)
		{
			ilt.add_deref(new_field);
//			ilt.add_deref(++new_field);
			n.set_var_id(get_var_id());
			n.set_ind_list(ilt);
		
			n.add_node_map();

			return n;
		}

		vi = cs_first_vi_for_offset(VEC_index(csvarinfo_t, csvarmap, vid), *it);		

		if(vi)
		{
			vid = vi->id;
		
			n.set_var_id(vid);
			
			ilt = il1.pop_deref_list();

			if(type == LL && ilt.length() == 0)
			{
				ilt.add_deref(NDEREF);
			}

			n.set_ind_list(ilt);

			n.add_node_map();

			return n;
		}
		else
		{
			return *this;
		}
	}

	return *this;
}

bool Node::check_if_temp()
{
//	fprintf(dump_file,"\nInside check_if_temp\n");

	unsigned int var_id = get_var_id();

	if(var_id <= 3)
	{
		return false;
	}

	tree decl = VEC_index(csvarinfo_t, csvarmap, get_var_id())->decl;

	if(!decl)
	{
		return false;
	}

	if(DECL_ARTIFICIAL(decl))
	{
		return true;
	}
	else
	{
		return false;
	}

}

// Edge APIs

Edge::Edge(Node l, Node r)
{
	set_lhs(l);
	set_rhs(r);

	compute_edge_id();
}

Node Edge::get_lhs()
{
	return lhs;
}

Node Edge::get_rhs()
{
	return rhs;
}

edge_id Edge::get_edge_id()
{
	return eid;
}

void Edge::set_lhs(Node l)
{
	lhs = l;
}

void Edge::set_rhs(Node r)
{
	rhs = r;
}

void Edge::set_edge_id(edge_id id)
{
	eid = id;
}

void Edge::compute_edge_id()
{
	Node lhs = get_lhs();
	Node rhs = get_rhs();

	edge_id id = make_tuple(lhs.get_node_id(), rhs.get_node_id());

	set_edge_id(id);
}

bool operator<(const Edge & e1, const Edge & e2)
{
	if(e1.eid < e2.eid)
		return true;

	return false;

}

bool operator==(const Edge & e1, const Edge & e2)
{
	if(e1.eid == e2.eid)
		return true;
	
	return false;

}

bool Edge::is_infinity()
{
	return (get_lhs().get_ind_list().is_infinity() || get_rhs().get_ind_list().is_infinity());
}

bool Edge::can_compose()
{
	if(is_self_loop())
	{
		return true;
	}
	else if(global_var(get_lhs().get_var_id()))
	{
		if(get_rhs().get_ind_list().length() <= 1)
		{
			return true;
		}
		else
		{
			return false;
		}	
	}
	else
	{
		return true;
	}
}

bool Edge::is_self_loop()
{
	il il1, il2;

	il1.add_deref(NDEREF);

	for(int i = 0; i < infi_thresh; i++)
	{
		il2.add_deref(NDEREF);
	}
	
	il2.set_infinity();

	Node lhs, rhs;

	lhs = get_lhs();
	rhs = get_rhs();

	if(lhs.get_var_id() == rhs.get_var_id())
	{
		if(lhs.get_ind_list().is_eq(il1))
		{
			if(rhs.get_ind_list().is_eq(il2))
			{
				return true;
			}
		}
	
		return false;
	}

	return false;
}

void Edge::print_edge()
{
	Node l,r;

	l = get_lhs();
	r = get_rhs();

	fprintf(dump_file,"\nEdge\n");
//	fprintf(dump_file,"\nLHS Node\n");
	l.print_node();
//	fprintf(dump_file,"\nRHS Node\n");
	r.print_node();
}

bool Edge::is_con_dep_edge()
{
	unsigned int lhs, rhs;

	lhs = get_lhs().get_var_id();
	rhs = get_rhs().get_var_id();

	if(CDV.find(lhs) != CDV.end() || CDV.find(rhs) != CDV.end())
	{
		return true;
	}

	return false;
}

bool Edge::is_boundary_edge()
{
//	fprintf(dump_file,"\nInside is_boundary_edge\n");

	il il1, il2;

	il1.add_deref(-1); // il for x->x' edge

	for(int i = 0; i < infi_thresh; i++)
	{
		il2.add_deref(-1);
	}	

	il2.set_infinity(); // il for x'->x' edge

	Node lhs = get_lhs();
	Node rhs = get_rhs();

	#if 0
	unsigned int var = lhs.get_var_id();

	if(global_var(var))
	{
		return false;
	}
	#endif	

	if((lhs.get_var_id() == (rhs.get_var_id()-1)) && (CDV.find(rhs.get_var_id()) != CDV.end()))
	{
//		fprintf(dump_file,"\nx -> x'\n");

		if(lhs.get_ind_list().is_eq(il1) && lhs.get_ind_list().is_eq(il1))
		{
//			fprintf(dump_file,"\nIL Check\n");
			return true;
		}
	}
	else if((lhs.get_var_id() == rhs.get_var_id()) && (CDV.find(rhs.get_var_id()) != CDV.end()))
	{
//		fprintf(dump_file,"\nx' -> x'\n");

		if(lhs.get_ind_list().is_eq(il1) && rhs.get_ind_list().is_eq(il2))
		{
//			fprintf(dump_file,"\nIL Check\n");
			return true;
		}
	}

//	fprintf(dump_file,"\nNo Boundary Edge\n");

	return false;

}

bool Edge::is_stack_edge()
{
	Edge e = *this;

	Node lhs, rhs;

	lhs = e.get_lhs();
	rhs = e.get_rhs();

	il_type temp1, temp2;

	temp1 = lhs.get_ind_list().get_deref_list();
	temp2 = rhs.get_ind_list().get_deref_list();

	if(temp1.size() >= 2 && temp1[1] != NDEREF)
	{
//		fprintf(dump_file,"\nLHS Heap, ind > 2\n");
		return false;
	}

	if(temp2.size() >= 2 && temp2[1] != NDEREF)
	{
//		fprintf(dump_file,"\nRHS Heap, ind > 2\n");
		return false;
	}

	if(!unexpandable_var(lhs.get_var_id(), 0))
	{
//		fprintf(dump_file,"\nLHS Heap\n");
		return false;
	}	

	if(!unexpandable_var(rhs.get_var_id(), 0))
	{
//		fprintf(dump_file,"\nRHS Heap\n");
		return false;
	}	

//	fprintf(dump_file,"\nStack\n");
	return true;

	#if 0
	if(temp1.size() < 2 || temp2.size() < 2)
	{
		if((!unexpandable_var(lhs.get_var_id(), 0)) || (!unexpandable_var(rhs.get_var_id(), 0)))
		{
			fprintf(dump_file,"\nHeap Edge\n");
			return false;
		}
		else
		{
			return true;
		}
	}	

	if(temp1[1] != NDEREF || temp2[1] != NDEREF)
	{
		return false;
	}
	else
	{
		return true;
	}
	#endif
}

// DVG APIs

tuple< set_edges, set_edges > DVG::separate_stack_heap() // First = Stack, Second = Heap
{
	set_edges elist, elist1, elist2;

	elist = get_edge_list();

	edge_it it;
	Edge e;

	for(it = elist.begin(); it != elist.end(); it++)
	{
		e = get_edge(*it);

		if(e.is_stack_edge())
		{
			elist1.insert(*it);
		}
		else
		{
			elist2.insert(*it);
		}
	}

	tuple< set_edges, set_edges > temp = make_tuple(elist1, elist2);

	return temp;
}

bool DVG::is_top()
{
	return top;
}

void DVG::set_top()
{
	top = true;
}

void DVG::reset_top()
{
	top = false;
}

var_list DVG::get_node_list()
{
	return node_list;
}

set_edges DVG::get_edge_list()
{
	return edge_list;
}

var_incom_out DVG::get_node_edge_map()
{
	return node_edge_map;
}

void DVG::set_node_list(var_list vl)
{
	node_list = vl;
}

void DVG::set_edge_list(set_edges se)
{
	edge_list = se;
}

void DVG::set_node_edge_map(var_incom_out vio)
{
	node_edge_map = vio;
}

bool operator<(const DVG & g1, const DVG & g2)
{
	if(g1.edge_list < g2.edge_list)
		return true;
	
	return false;

}

bool operator==(const DVG & g1, const DVG & g2)
{
	if(g1.edge_list == g2.edge_list)
		return true;
	
	return false;

}

set_edges DVG::compat_edges(Node p, bool kill, struct cgraph_node *cnode)
{
	#if TRACE
//	fprintf(dump_file,"\nInside compat_edges\n");
	#endif

//	fprintf(dump_file,"\nDVG\n");
//	print_node_edge_map();

	set_edges out_edges = get<1>(get_node_edge_map()[p.get_var_id()]);

//	fprintf(dump_file,"\nOutgoing Edges of Node...\n");
//	print_set_edges(out_edges);

//	fprintf(dump_file,"\nNumber of Outgoing Edges %d\n",out_edges.size());
//	fprintf(dump_file,"\nOutgoing Edges of %s\n",get_var_name(p.get_var_id()));

//	print_set_edges(out_edges); 

	#if 0
	if(kill)
		fprintf(dump_file,"\nLHS\n");
	else
		fprintf(dump_file,"\nRHS\n");
	#endif

	edge_it eit;

	set_edges temp;

	Edge e;
	Node lhs;

	for(eit=out_edges.begin(); eit != out_edges.end(); eit++)
	{
		e = get_edge(*eit);

		lhs = e.get_lhs();

		if(kill && lhs.node_eq(p))
		{
//			fprintf(dump_file,"\nTo Be Killed and Not Composed\n");
			continue;
		}

//		fprintf(dump_file,"\nLHS of the would be compatible edge\n");
//		lhs.print_node();

		#if 0
		if(e.can_compose())
		{
			e.print_edge();
			fprintf(dump_file,"\nCan Compose Condition 2 True\n");
		}
		#endif

		if(lhs.sim(p) && e.can_compose())
		{
//			fprintf(dump_file,"\nComposition Possible\n");
			temp.insert(*eit);
		}
		
	}

	return temp;
}

void DVG::add_edges_fi_dvg(set_edges elist, struct cgraph_node *cnode)
{
	edge_it eit;

	var_list nodes = get_node_list();
	set_edges edges = get_edge_list();
	var_incom_out nodes_edges = get_node_edge_map();

	tuple< set_edges, set_edges > map_entry;
	set_edges temp_in, temp_out;
	Edge e;
	unsigned int lhs_var, rhs_var;
	set_edges temp_edges;

//	DVG fi_dvg = ((function_info *)(cnode->aux))->get_fi_dvg();

	for(eit=elist.begin(); eit != elist.end(); eit++)
	{
		e =  get_edge(*eit);

		lhs_var = e.get_lhs().get_var_id();

		rhs_var = e.get_rhs().get_var_id();

		edges.insert(*eit);  // Updated edge list

		nodes.insert(lhs_var);  // Updated node list
		nodes.insert(rhs_var);

		map_entry = nodes_edges[lhs_var];  // Update node-edge map

		temp_in = get<0>(map_entry);
		temp_out = get<1>(map_entry);
		temp_out.insert(*eit);

		map_entry = make_tuple(temp_in,temp_out);
		nodes_edges[lhs_var] = map_entry;

		map_entry = nodes_edges[rhs_var];
		
		temp_in = get<0>(map_entry);
		temp_out = get<1>(map_entry);
		temp_in.insert(*eit);

		map_entry = make_tuple(temp_in, temp_out);
		nodes_edges[rhs_var] = map_entry;

	}

	set_node_list(nodes);
	set_edge_list(edges);
	set_node_edge_map(nodes_edges);	

//	((function_info *)(cnode->aux))->set_fi_dvg(fi_dvg);
}

void DVG::add_edges(basic_block bb, set_edges elist, struct cgraph_node *cnode, unsigned int cons_id, bool data)
{
//	fprintf(dump_file,"\nInside add_edges...\n");

//	fprintf(dump_file,"\nBefore Adding\n");
//	print_node_edge_map();
	
	#if STATS	
	add_edges_func_count++;

	starttime();
	#endif
	
	edge_it eit;

	var_list nodes = get_node_list();
	set_edges edges = get_edge_list();
	var_incom_out nodes_edges = get_node_edge_map();

	tuple< set_edges, set_edges > map_entry;
	set_edges temp_in, temp_out;
	Edge e;
	unsigned int lhs_var, rhs_var;
	set_edges temp_edges;
	unsigned int ret_id = ((function_info *)(cnode->aux))->get_ret_id();

	DVG fi_dvg = ((function_info *)(cnode->aux))->get_fi_dvg();

	for(eit=elist.begin(); eit != elist.end(); eit++)
	{
		e =  get_edge(*eit);

		lhs_var = e.get_lhs().get_var_id();

		if(lhs_var == undef_id || lhs_var == nothing_id)
		{
			continue;
		}

//		e.print_edge();
		#if STATS
		add_edge_count++;

//		fprintf(dump_file,"\nAdding Composed Edge so far %d\n", add_edge_count);
//		e.print_edge();
		#endif
		
		#if 1
		if(e.get_lhs().check_if_temp() && lhs_var != ret_id)
		{
//			fprintf(dump_file,"\nTemp Edge\n");
//			e.print_edge();
			temp_edges.insert(*eit);
			continue;
		}
		#endif

//		fprintf(dump_file,"\nHiiiiii\n");

		rhs_var = e.get_rhs().get_var_id();

		edges.insert(*eit);  // Updated edge list

		nodes.insert(lhs_var);  // Updated node list
		nodes.insert(rhs_var);

		map_entry = nodes_edges[lhs_var];  // Update node-edge map

		temp_in = get<0>(map_entry);
		temp_out = get<1>(map_entry);
		temp_out.insert(*eit);

		map_entry = make_tuple(temp_in,temp_out);
		nodes_edges[lhs_var] = map_entry;

		map_entry = nodes_edges[rhs_var];
		
		temp_in = get<0>(map_entry);
		temp_out = get<1>(map_entry);
		temp_in.insert(*eit);

		map_entry = make_tuple(temp_in, temp_out);
		nodes_edges[rhs_var] = map_entry;


		if(data)
		{
			continue;
		}

		if(((function_info *)(cnode->aux))->orig_rev_order_map[*eit] == 0)		
		{
			((function_info *)(cnode->aux))->orig_rev_order_map[*eit] = cons_id;
		}
		else
		{
			((block_information *)(bb->aux))->order_out[*eit] = cons_id;	
		}

		if(!e.is_boundary_edge())
		{
//			fprintf(dump_file,"\nNot a Boundary Edge\n");
			map<edge_id, unsigned int> edge_ord = ((function_info *)(cnode->aux))->get_rev_order_map();

			edge_ord[*eit] = cons_id;

			((function_info *)(cnode->aux))->set_rev_order_map(edge_ord);

			map<unsigned int, set_edges> ord = ((function_info *)(cnode->aux))->get_order_map();
			temp_edges = ord[cons_id];

			temp_edges.insert(*eit);

			ord[cons_id] = temp_edges;
			((function_info *)(cnode->aux))->set_order_map(ord);

//			((function_info *)(cnode->aux))->set_edge_id_map(((function_info *)(cnode->aux))->increment_order_id(), *eit);
//			((function_info *)(cnode->aux))->set_edge_id_map_rev(((function_info *)(cnode->aux))->increment_order_id(), *eit);
		}
	}

	set_node_list(nodes);
	set_edge_list(edges);
	set_node_edge_map(nodes_edges);	

	((function_info *)(cnode->aux))->orig_order_map[cons_id] =  elist;

	fi_dvg.add_edges_fi_dvg(temp_edges, cnode);
	((function_info *)(cnode->aux))->set_fi_dvg(fi_dvg);

	#if STATS
	temp_time = stoptime();

	add_edges_time += temp_time;	

//	fprintf(dump_file,"\nadd_edges: Called %d times so far, Overall Time Taken: %lg, Time Taken for this Call %lg\n", add_edges_func_count, add_edges_time, temp_time);
	#endif

//	fprintf(dump_file,"\nAfter Adding\n");
//	print_node_edge_map();
	
}

bool DVG::weaker(DVG g2, struct cgraph_node *cnode) // g1 <= g2 i.e Is g1 weaker than g2
{
	set_edges elist1 = get_edge_list();
	set_edges elist2 = g2.get_edge_list();
	 
	edge_it it1, it2;
	Edge e1, e2;
	set_edges temp1, temp2;

	for(it2 = elist2.begin(); it2 != elist2.end(); it2++)
	{
		e2 = get_edge(*it2);

		if(e2.is_boundary_edge())
		{
			continue;
		}

		if(elist1.find(*it2) == elist1.end())
		{
			temp1 = compat_edges(e2.get_lhs(), false, cnode);
		
			temp2 = compat_edges(e2.get_rhs(), true, cnode);
				

			if(temp1.empty() && temp2.empty())
			{
				return false;
			}
		}
	}

	return true;
}

void DVG::remove_edges_fi_dvg(set_edges elist, struct cgraph_node *cnode)
{
	edge_it eit;
	map<unsigned int, edge_id>::iterator mit;

	set_edges temp_edges;

	var_list nodes = get_node_list();
	set_edges edges = get_edge_list();
	var_incom_out nodes_edges = get_node_edge_map();

	tuple< set_edges, set_edges > map_entry;
	set_edges temp_in, temp_out;
	Edge e;
	unsigned int lhs_var, rhs_var;

//	DVG fi_dvg = ((function_info *)(cnode->aux))->get_fi_dvg();

	for(eit=elist.begin(); eit != elist.end(); eit++)
	{
		e = get_edge(*eit);
//		fprintf(dump_file,"\nEdge To Be Killed\n");
//		e.print_edge();

		lhs_var = e.get_lhs().get_var_id();
		rhs_var = e.get_rhs().get_var_id();

		edges.erase(*eit); // Updated edge_list;	

		map_entry = nodes_edges[lhs_var];
		temp_in = get<0>(map_entry);
		temp_out = get<1>(map_entry);
		temp_out.erase(*eit);

		map_entry = make_tuple(temp_in, temp_out);

		nodes_edges[lhs_var] = map_entry;

		if(temp_in.empty() && temp_out.empty())
		{
			nodes.erase(lhs_var);
		}


		map_entry = nodes_edges[rhs_var];
		temp_in = get<0>(map_entry);
		temp_out = get<1>(map_entry);
		temp_in.erase(*eit);

		map_entry = make_tuple(temp_in, temp_out);

		nodes_edges[rhs_var] = map_entry;

		if(temp_in.empty() && temp_out.empty())
		{
			nodes.erase(rhs_var);
		}

	}

	set_node_list(nodes);
	set_edge_list(edges);
	set_node_edge_map(nodes_edges);

//	fprintf(dump_file,"\nAfter Removing\n");
//	print_node_edge_map();
	
//	((function_info *)(cnode->aux))->set_fi_dvg(fi_dvg);
}

void DVG::remove_edges(basic_block bb, set_edges elist, struct cgraph_node *cnode, bool data)
{
//	fprintf(dump_file,"\nInside remove_edges\n");

//	fprintf(dump_file,"\nBefore Removing\n");
//	print_node_edge_map();

	#if STATS	
	remove_edges_func_count++;

	starttime();
	#endif
	
	edge_it eit;
	map<unsigned int, edge_id>::iterator mit;

	set_edges temp_edgesx;

	var_list nodes = get_node_list();
	set_edges edges = get_edge_list();
	var_incom_out nodes_edges = get_node_edge_map();

	tuple< set_edges, set_edges > map_entry;
	set_edges temp_in, temp_out;
	Edge e;
	unsigned int lhs_var, rhs_var;

	DVG fi_dvg = ((function_info *)(cnode->aux))->get_fi_dvg();

	for(eit=elist.begin(); eit != elist.end(); eit++)
	{
		e = get_edge(*eit);
//		fprintf(dump_file,"\nEdge To Be Killed\n");
//		e.print_edge();

		#if STATS
		delete_edge_count++;	

//		fprintf(dump_file,"\nKilling an Edge so far %d\n", delete_edge_count);
		#endif
	
		#if 1
		if(e.get_lhs().check_if_temp())
		{
			temp_edgesx.insert(*eit);
			continue;
		}
		#endif

		lhs_var = e.get_lhs().get_var_id();
		rhs_var = e.get_rhs().get_var_id();

		edges.erase(*eit); // Updated edge_list;	

		map_entry = nodes_edges[lhs_var];
		temp_in = get<0>(map_entry);
		temp_out = get<1>(map_entry);
		temp_out.erase(*eit);

		if(temp_in.empty() && temp_out.empty())
		{
			nodes.erase(lhs_var);
		}

		map_entry = make_tuple(temp_in, temp_out);

		nodes_edges[lhs_var] = map_entry;

		map_entry = nodes_edges[rhs_var];
		temp_in = get<0>(map_entry);
		temp_out = get<1>(map_entry);
		temp_in.erase(*eit);

		if(temp_in.empty() && temp_out.empty())
		{
			nodes.erase(rhs_var);
		}

		map_entry = make_tuple(temp_in, temp_out);

		nodes_edges[rhs_var] = map_entry;

		if(data)
		{
			continue;
		}	
	
		unsigned int order = ((function_info *)(cnode->aux))->get_order_edge(*eit);

		map<edge_id, unsigned int> edge_ord = ((function_info *)(cnode->aux))->get_rev_order_map();

		edge_ord.erase(*eit);

		((function_info *)(cnode->aux))->set_rev_order_map(edge_ord);

		map<unsigned int, set_edges> ord = ((function_info *)(cnode->aux))->get_order_map();

		set_edges temp_edges = ord[order];

		temp_edges.erase(*eit);

		if(temp_edges.empty())
		{
			ord.erase(order);
		}
		else
		{
			ord[order] = temp_edges;
		}

		((function_info *)(cnode->aux))->set_order_map(ord);
	}

	set_node_list(nodes);
	set_edge_list(edges);
	set_node_edge_map(nodes_edges);

//	fprintf(dump_file,"\nAfter Removing\n");
//	print_node_edge_map();
	
//	fprintf(dump_file,"\nFlow Insensitive DVG Before Kill\n");
//	fi_dvg.print_dvg();
	
	fi_dvg.remove_edges_fi_dvg(temp_edgesx, cnode);
	((function_info *)(cnode->aux))->set_fi_dvg(fi_dvg);

	#if STATS
	temp_time = stoptime();

	remove_edges_time += temp_time;	

//	fprintf(dump_file,"\nremove_edges: Called %d times so far, Overall Time Taken: %lg, Time Taken for this Call %lg\n", remove_edges_func_count, remove_edges_time, temp_time);
	#endif

//	fprintf(dump_file,"\nFlow Insensitive DVG After Kill\n");
//	fi_dvg.print_dvg();
	
	
}

DVG DVG::copy_dvg()
{
        DVG g; // = new DVG();
        g.node_list = get_node_list();
        g.edge_list = get_edge_list();
        g.node_edge_map = get_node_edge_map();

        return g;
}

void DVG::print_dvg()
{
	set_edges elist = get_edge_list();
	Edge e;
	edge_it eit;
	Node lhs, rhs;

	unsigned int lhs_var, rhs_var;
	const char *nn = "i";
       	const char *name1,*fname1,*name2,*fname2;
	string str1,str2;

//	fprintf(dump_file,"\nDVG\n");

//	fprintf(dump_file,"\nEdge List Size %d\n",elist.size());

	for(eit=elist.begin(); eit != elist.end(); eit++)
	{
//		fprintf(dump_file,"\nPrinting Edge\n");	
		e = get_edge(*eit);
//		e.print_edge();

		lhs = e.get_lhs();
		rhs = e.get_rhs();

		lhs_var = lhs.get_var_id();
		rhs_var = rhs.get_var_id();

		fname1 = copy_string(VEC_index(csvarinfo_t, csvarmap, lhs_var)->name);

		if(CDV.find(lhs_var) != CDV.end())
		{
        		name1 = copy_string(VEC_index(csvarinfo_t, csvarmap, lhs_var)->name);
	                str1 = string(name1) + string(nn);
        	        fname1 = copy_string(str1.c_str());
		}
		
		fname2 = copy_string(VEC_index(csvarinfo_t, csvarmap, rhs_var)->name);

		if(CDV.find(rhs_var) != CDV.end())
		{
        		name2 = copy_string(VEC_index(csvarinfo_t, csvarmap, rhs_var)->name);
	                str2 = string(name2) + string(nn);
        	        fname2 = copy_string(str2.c_str());
		}

//		fprintf(dump_file,"\n%s -> %s (%d, %d)\n", fname1, fname2, lhs.get_ind_list().length(), rhs.get_ind_list().length());
//		fprintf(dump_file,"\n%d -> %d (%d, %d)\n", lhs_var, rhs_var, lhs.get_ind_list().length(), rhs.get_ind_list().length());

//		lhs.get_ind_list().print_il();
//		rhs.get_ind_list().print_il();

		print_node_id(lhs.get_node_id());
		print_node_id(rhs.get_node_id());
		
	}
//	fprintf(dump_file,"\nPrinting Done\n");
}

set_nodes DVG::compose(node_id nid, int type, struct cgraph_node *cnode) // type == 1 => LR composition, type == 2 => LL composition
{
	Node p = get_node(nid);

	set_nodes composed_nodes;

//	fprintf(dump_file,"\nInside compose\n");
//	p.print_node();


//	fprintf(dump_file,"\nType of Composition %d\n",type);

	#if 0
	fprintf(dump_file,"\nLHS of Edge\n");	
	print_node_id(e.get_lhs().get_node_id());

	fprintf(dump_file,"\nRHS of Edge\n");	
	print_node_id(e.get_rhs().get_node_id());
	#endif

	if(type == LR)
	{
		if(p.get_ind_list().length() == 0)
		{
//			fprintf(dump_file,"\nBase Condition - RHS\n");
			composed_nodes.insert(nid);
			return composed_nodes;
		}
	}
	else if(type == LL)
	{
		if(p.get_ind_list().length() == 1)
		{
//			fprintf(dump_file,"\nBase Condition - LHS\n");
			composed_nodes.insert(nid);
			return composed_nodes;
		}
	}

	bool kill = false;

	edge_it eit;

	if(type == LL)
	{
		kill = true;
	}

	DVG fi_dvg = ((function_info *)(cnode->aux))->get_fi_dvg();

	set_edges elist;

	#if 1
	if(p.check_if_temp())
	{
		elist = fi_dvg.compat_edges(p,kill, cnode);
	}	
	else
	{		
		elist = compat_edges(p, kill, cnode);
	}
	#endif

//	elist = compat_edges(p, kill, cnode);

//	fprintf(dump_file,"\nNo. of Compatible Edges %d\n",elist.size());
//	print_set_edges(elist);
	
	if(elist.empty())
	{
		composed_nodes.insert(nid);

		#if 0
		if(type == LL)
		{
			may_info_lhs.insert(nid);
		}
		else
		{
			may_info_rhs.insert(nid);
		}
		return composed_nodes;
		#endif
	}	

//	fprintf(dump_file,"\nCompatible Edges\n");
//	print_set_edges(elist);

//	fprintf(dump_file,"\nelist size %d\n",elist.size());

	Node t;

	Edge new_edge, e1;
	edge_id eid;

	for(eit=elist.begin(); eit != elist.end(); eit++)
	{
		e1 = get_edge(*eit);

//		fprintf(dump_file,"\nIn compose edge\n");
//		e1.print_edge();
	
		if(e1.is_self_loop() && CDV.find(p.get_var_id()) != CDV.end())
		{
//			fprintf(dump_file,"\nComposition with Self Loop\n");

			#if 0
			if(type == LR)
			{
//				fprintf(dump_file,"\nControl Here\n");
//				get_node(nid).print_node();
//				may_info_rhs.insert(nid);
				composed_nodes.insert(nid);
				nodes_visited.insert(nid);
			}
			else if(type == LL)
			{
//				may_info_lhs.insert(nid);
				composed_nodes.insert(nid);
				nodes_visited.insert(nid);
			}
			#endif

			composed_nodes.insert(nid);
			nodes_visited.insert(nid);

			continue;
		}
//		else if(type == LL && p.node_eq(e1.get_lhs()))
		{
//			continue;
		}

//		fprintf(dump_file,"\nHiiiii\n");

		t = p.construct_new_node(*eit, type);

//		fprintf(dump_file,"\nHelloooo\n");

//		fprintf(dump_file,"\nConstructed new node\n");
//		t.print_node();

		if(nodes_visited.find(t.get_node_id()) != nodes_visited.end())
		{
			#if 0
			if(type == LR)
			{
				may_info_rhs.insert(nid);
			}
			else if(type == LL)
			{
				may_info_lhs.insert(nid);
			}
			#endif	

			composed_nodes.insert(nid);

			continue;
		}
		else
		{
			nodes_visited.insert(t.get_node_id());

//			fprintf(dump_file,"\nConstructed new node\n");
//			t.print_node();

			composed_nodes.insert(t.get_node_id());

		}
	}

//	fprintf(dump_file,"\nPrinting Return Value of Compose\n");
//	print_set_node_ids(composed_nodes);
	return composed_nodes;
}

set_nodes DVG::single_composition(set_nodes g2, int type, struct cgraph_node *cnode)
{
	set_nodes composed_nodes, temp;

	Node_it nit;

	for(nit = g2.begin(); nit != g2.end(); nit++)
	{
		temp = compose(*nit, type, cnode);

		composed_nodes.insert(temp.begin(), temp.end());
	}
	
	return composed_nodes;
}

set_nodes DVG::trans(set_nodes S, int type, struct cgraph_node *cnode)
{
	set_nodes temp = single_composition(S, type, cnode);
	Node_it it;

//	fprintf(dump_file,"\nSet S\n");
//	print_set_node_ids(S);

	if((temp == S) || temp.empty())
	{
//		it = temp.begin();
//		fprintf(dump_file,"\nBase Condition - trans\n");
//		if(S.find(*it) != S.end())
//		print_set_node_ids(S);
		return S;
	}
	else
	{
//		fprintf(dump_file,"\nRecursive Call to trans\n");
		return trans(temp, type, cnode);
	}
}

void DVG::generate_graph(basic_block bb, constraint_t con, struct cgraph_node *cnode, unsigned int cons_id)
{
	#if TRACE
//	fprintf(dump_file,"\nInside generate_graph\n");
	#endif
	
	if(con->rhs.ptr_arith && !con->heap_alloc)
        {
                #if TRACE
                {
//                fprintf(dump_file,"\nPointer Arithmetic\n");
                }
                #endif

                con->rhs.var = 0;
                con->rhs.type = 0;
                con->rhs.offset = 0;

		#if STATS
		tree lhsop, rhsop;

		lhsop = VEC_index (csvarinfo_t, csvarmap, con->lhs.var)->decl;
		rhsop = VEC_index (csvarinfo_t, csvarmap, con->lhs.var)->decl;

		if(AGGREGATE_TYPE_P (TREE_TYPE (TREE_TYPE (lhsop)))) // || AGGREGATE_TYPE_P (TREE_TYPE (lhsop)))
			ptr_arith_count_heap++;
		else
			ptr_arith_count_stack++;
		#endif
        }


        if(con->lhs.var == undef_id || con->lhs.var == nothing_id || con->lhs.var == escaped_id || con->lhs.var == readonly_id)
                return;

        if(con->rhs.var == escaped_id || con->rhs.var == readonly_id)
//        if(con->rhs.var == nothing_id || con->rhs.var == escaped_id || con->rhs.var == readonly_id)
                return;

//	fprintf(dump_file,"\nChecking Done\n");
//	fprintf(dump_file,"\nDVG\n");
//	print_dvg();

//	temp_il_edges.clear();
	DVG callee_dvg;

	if((!unexpandable_var(con->lhs.var, con->lhs.offset) || !unexpandable_var(con->rhs.var, con->rhs.offset)) && infi_thresh < 2)
	{
//		fprintf(dump_file,"\nStatement Ignored\n");
		#if TRACE
//		fprintf(dump_file,"\nStatement Ignored\n");
		#endif
		return;
	}

	Edge e(Node(con->lhs,cons_id), Node(con->rhs,cons_id));

	#if STATS
	constraint_edge_count++;
	#endif

	edge_id id = e.get_edge_id();

//	fprintf(dump_file,"\nEdge to be Added...\n");
//	e.print_edge();	

	set_edges gen, killed, subsumed;

	gen = edge_comp(id, cnode);

//	gen = update_gen(gen);

//	fprintf(dump_file,"\nPrinting Gen...\n");
	
//	print_set_edges(gen);

	killed = kill(gen, id, cnode, callee_dvg);

//	fprintf(dump_file,"\nKill Computed\n");

//	print_set_edges(killed);

	remove_edges(bb, killed, cnode, false);
	add_edges(bb, gen, cnode, cons_id, false);
		
//	print_dvg();
}

void DVG::func_comp(basic_block bb, Edge e, struct cgraph_node *cnode, unsigned int cons_id, DVG callee_dvg, struct cgraph_node *node, bool data)
{
	#if STATS
	func_comp_count++;

	starttime();
	#endif

	edge_id id = e.get_edge_id();

//	fprintf(dump_file,"\nEdge to be Added...\n");
//	e.print_edge();	

	set_edges gen, killed, subsumed;

	gen = edge_comp(id, cnode);

//	fprintf(dump_file,"\nHelloooo\n");

//	gen = update_gen(gen);

//	fprintf(dump_file,"\nPrinting Gen...\n");
	
//	print_set_edges(gen);

	if(((function_info *)(cnode->aux))->count > 2)   // Function composition with no kill if function is being processed more than twice
	{
	killed = kill(gen, id, cnode, callee_dvg);

	edge_it eit;
	set_edges remove, elist;
	set_edges callee_edges = callee_dvg.get_edge_list();

	for(eit = killed.begin(); eit != killed.end(); eit++)
	{
		if(callee_edges.find(*eit) != callee_edges.end())
		{
//			if(((function_info *)(node->aux))->get_order_edge(*eit) == cons_id)
			{
				remove.insert(*eit);
			}
		}
	}

	set_difference(killed.begin(), killed.end(), remove.begin(), remove.end(), inserter(elist, elist.end()));

//	fprintf(dump_file,"\nKill Computed\n");

//	print_set_edges(elist);

	remove_edges(bb,elist, cnode, data);
	}

//	fprintf(dump_file,"\nBefore Call to add_edges\n");
	add_edges(bb, gen, cnode, cons_id, data);
		
//	print_dvg();

	#if STATS
	temp_time = stoptime();

	func_comp_time += temp_time;

//	fprintf(dump_file,"\nFunction Composition: Called %d times so far, Overall Time Taken: %lg, Time Taken for this Call %lg\n", func_comp_count, func_comp_time, temp_time);
	#endif
	
}


set_edges DVG::update_gen(set_edges gen)
{
	set_edges temp1, temp2, temp3, temp;

	temp1 = gen;

	edge_it it;

	for(it = temp1.begin(); it != temp1.end(); it++)
	{
		temp2 = kill_subsumed_edges_from_list(gen,*it);

		temp3.insert(temp2.begin(), temp2.end());
	}

	set_difference(temp1.begin(), temp1.end(), temp3.begin(), temp3.end(), inserter(temp, temp.end()));

	return temp; 
}

set_edges DVG::kill_subsumed_edges_from_list(set_edges gen, edge_id id)
{
	edge_it it;

	Edge e1, e2;

	set_edges temp;

	e1 = get_edge(id);

	if(e1.is_self_loop() || !(e1.is_infinity()))
	{
		return temp;
	}	
	
	for(it = gen.begin(); it != gen.end(); it++)
	{
		e2 = get_edge(*it);

		if((e2.get_lhs().sim(e1.get_lhs())) && (e2.get_rhs().sim(e1.get_rhs())))	
		{
			temp.insert(*it);
		}
	}

	return temp;
}

set_edges DVG::edge_comp(edge_id id, struct cgraph_node *cnode)
{
//	print_node_edge_map();
//	fprintf(dump_file,"\nPrinting node-edge-map done\n");

	#if STATS
	edge_comp_count++;

	starttime();
//	fprintf(dump_file,"\nStart Time %ld\n",t_start.tv_sec);
	#endif

	Edge e = get_edge(id);

//	fprintf(dump_file,"\nHow do you do?\n");

	DVG g = ((function_info *)(cnode->aux))->get_fi_dvg();
//	fprintf(dump_file,"\nFlow Insensitive DVG\n");
//	g.print_dvg();

	Node lhs, rhs;

	lhs = e.get_lhs();

	rhs = e.get_rhs();

	set_nodes temp1, temp2, n_temp;

//	may_info_lhs.clear();
//	may_info_rhs.clear();

	nodes_visited.clear();

	n_temp.insert(lhs.get_node_id());

	#if 1
	if(lhs.check_if_temp())
	{	
		temp1 = g.trans(n_temp, LL, cnode);
	}
	else
	{	
		temp1 = trans(n_temp, LL, cnode);
	}
	#endif

//	temp1 = trans(n_temp, LL, cnode);

	nodes_visited.clear();
	n_temp.clear();
	n_temp.insert(rhs.get_node_id());

	#if 1
	if(rhs.check_if_temp())
	{
//		fprintf(dump_file,"\nTemp\n");
	
		temp2 = g.trans(n_temp, LR, cnode);
	}
	else
	{	
//		fprintf(dump_file,"\nNot Temp\n");
	
		temp2 = trans(n_temp, LR, cnode);
	}
	#endif

//	temp2 = trans(n_temp, LR, cnode);

//	fprintf(dump_file,"\nHere I go\n");

//	fprintf(dump_file,"\nPrinting RHS Nodes...\n");
//	print_set_node_ids(temp2);

	set_edges temp;

	temp = cross_product(temp1, temp2);

	if(temp.empty())
	{
		temp.insert(id);
	}

//	print_set_edges(temp);

	#if STATS
	temp_time = stoptime();

//	fprintf(dump_file,"\nStop Time %ld\n",t_end.tv_sec);

	edge_comp_time += temp_time;
//	fprintf(dump_file,"\nedge_comp: Called %d times so far, Overall Time Taken: %lg, Time Taken for this Call %lg\n", edge_comp_count, edge_comp_time, temp_time);
	#endif

	return temp;
		
}

set_edges DVG::cross_product(set_nodes s1, set_nodes s2)
{
	set_edges temp;

//	fprintf(dump_file,"\nInside cross_product\n");

//	fprintf(dump_file,"\nLHS Nodes...\n");
//	print_set_node_ids(s1);	

//	fprintf(dump_file,"\nRHS Nodes...\n");
//	print_set_node_ids(s2);	

	Edge e;
	edge_id id;	

	Node_it nit1, nit2;
	Node n1, n2;

	for(nit1 = s1.begin(); nit1 != s1.end(); nit1++)
	{
		n1 = get_node(*nit1);

		if(n1.get_var_id() == undef_id || n2.get_var_id() == nothing_id)
		{
			continue;
		}

		for(nit2 = s2.begin(); nit2 != s2.end(); nit2++)
		{
			n2 = get_node(*nit2);

			if((*nit1) == (*nit2))
			{
				continue;
			}

			e.set_lhs(n1);
			e.set_rhs(n2);

			e.compute_edge_id();
			id = e.get_edge_id();

			temp.insert(id);
		
		}
	}

	return temp;
}

set_edges DVG::kill_edges(Node p, struct cgraph_node *cnode, DVG callee_dvg)
{
	DVG fi_dvg = ((function_info *)(cnode->aux))->get_fi_dvg();

	set_edges elist, kill_list;

	edge_it eit;

	if(callee_dvg.multiple_outgoing_edges(p))
	{
		return elist;
	}
	
	if(p.check_if_temp())
	{
		elist = fi_dvg.get_edge_list();
	}
	else
	{
		elist = get_edge_list();
	}

	for(eit=elist.begin(); eit != elist.end(); eit++)
	{
		Edge e = get_edge(*eit);

		if(p.node_eq(e.get_lhs()))
		{
//			fprintf(dump_file,"\nItheee\n");
			kill_list.insert(*eit);
		}
	}

	return kill_list;
}

set_nodes DVG::lhs_alias(set_edges gen, edge_id id, struct cgraph_node *cnode)
{
	set_nodes node_list; //, S;

//	Edge e = get_edge(id);

//	S.insert(e.get_lhs().get_node_id());

	edge_it it;
	Node n;
	Edge e;
	
	for(it = gen.begin(); it != gen.end(); it++)
	{
		e = get_edge(*it);

		n = e.get_lhs();

		node_list.insert(n.get_node_id());	
	}

	e = get_edge(id);

//	node_list = gen; //trans(S,LL);
	node_list.erase(e.get_lhs().get_node_id());
//	node_list.insert(may_info_lhs.begin(), may_info_lhs.end());

	return node_list;
}

set_edges DVG::strong_update(set_edges gen, edge_id id, struct cgraph_node *cnode, DVG callee_dvg)
{
	set_edges kill_list;

	set_nodes node_list = lhs_alias(gen, id, cnode);

//	Node p = get_edge(id).get_lhs();
	Node n;
	Node_it it;

	if(node_list.size() == 1)
	{
		it = node_list.begin();
		
		n = get_node(*it);
//		fprintf(dump_file,"\nKill Done\n");

//		if(n.check_if_temp())
//		if(!n.check_if_temp())
		{	
			kill_list = kill_edges(get_node(*it), cnode, callee_dvg);
		}

		return kill_list;
	}
	else
	{
		return kill_list;
	}	
}

set_edges DVG::isl(Node p, struct cgraph_node *cnode)
{
	edge_it eit;
	Edge e;
	set_edges temp;

	DVG fi_dvg = ((function_info *)(cnode->aux))->get_fi_dvg();
	set_edges elist;
		
	#if 0
	if(p.check_if_temp())
	{
		elist = fi_dvg.get_edge_list();
	}
	else
	{
		elist = get_edge_list();
	}
	#endif

	elist = get_edge_list();

	for(eit=elist.begin(); eit!= elist.end(); eit++)
	{
		e = get_edge(*eit);

		if(e.is_self_loop())
		{
			temp.insert(*eit);
		}
	}	
	
	return temp;
}

set_edges DVG::gsl(Node p, struct cgraph_node *cnode)
{
	set_edges temp,elist;
	Edge e;

	edge_it eit;

	elist = isl(p, cnode);
	unsigned int var;

	if(p.get_var_id() == undef_id || p.get_var_id() == nothing_id)
		return temp;

	for(eit=elist.begin(); eit != elist.end(); eit++)
	{
		e = get_edge(*eit);

		var = e.get_lhs().get_var_id();

		if(var == undef_id || var == nothing_id)
		{
			continue;
		}

		if(e.get_lhs().con_dep().get_var_id() == p.con_dep().get_var_id())
		{
			temp.insert(*eit);
		}

	}

	return temp;
}

set_edges DVG::kill_self_loop(set_edges gen, edge_id id, struct cgraph_node *cnode)
{
	set_nodes node_list = lhs_alias(gen, id, cnode);

	Edge e = get_edge(id);

	if(!e.get_lhs().check_if_temp())
	{
		node_list.insert(e.get_lhs().get_node_id());
	}

	Node_it it;

	set_edges kill_loops, temp;
	Node n;

	for(it=node_list.begin(); it != node_list.end(); it++)
	{
		n = get_node(*it);

		if(!n.check_if_temp())
		{
			temp = gsl(n, cnode);

			kill_loops.insert(temp.begin(), temp.end());
		}
	}

	return kill_loops;
}

set_edges DVG::kill_subsumed_edges(edge_id id)
{
	Edge e = get_edge(id);

//	fprintf(dump_file,"\nInside Kill subsumed edges\n");
//	e.print_edge();

	set_edges temp;
	
	if(e.is_self_loop())
	{
		return temp;
	}

	if(e.is_infinity())
	{
//		fprintf(dump_file,"\nKill subsumed edges\n");
		
		temp = subsumed_edges(id);

		temp.erase(id);
	}

	return temp;
}

set_edges DVG::subsumed_edges(edge_id id)
{
	set_edges subsumed_list, elist;

//	fprintf(dump_file,"\nInside subsumed edges\n");

	elist = get_edge_list();

	Edge e = get_edge(id);
	Edge etemp;

	#if 0

	if(e.is_infinity())
	{
		return subsumed_list;
	}
	#endif

//	fprintf(dump_file,"\nEdge 1\n");
//	e.print_edge();

	edge_it eit;

	for(eit=elist.begin(); eit != elist.end(); eit++)
	{
		etemp = get_edge(*eit);

//		fprintf(dump_file,"\nEdge 2\n");
//		etemp.print_edge();

		if((etemp.get_lhs().sim(e.get_lhs())) && (etemp.get_rhs().sim(e.get_rhs())))
		{
//			fprintf(dump_file,"\nCondition for Subsumption\n");
//			fprintf(dump_file,"\nEdge 2\n");
//			etemp.print_edge();

			subsumed_list.insert(*eit);
		}
	}

	return subsumed_list;
}

set_edges DVG::kill(set_edges gen, edge_id id, struct cgraph_node *cnode, DVG callee_dvg)
{
	#if STATS
	kill_count++;

	starttime();
	#endif
	
	Edge e = get_edge(id);

	set_edges temp, kill_list;

	if(check_array(e.get_lhs().get_var_id()))
	{
//		fprintf(dump_file,"\nArray Type. No Kill\n");
		return kill_list;
	}

//	if(!e.get_lhs().check_if_temp())
	{
		temp = kill_edges(e.get_lhs(), cnode, callee_dvg);    // Kill1 => Direct Kill
		kill_list.insert(temp.begin(),temp.end());
	}

	temp = strong_update(gen, id, cnode, callee_dvg);         // Kill1 => Indirect Kill
	kill_list.insert(temp.begin(),temp.end());

	temp = kill_self_loop(gen, id, cnode);        // Kill3 => Self Loops
	kill_list.insert(temp.begin(),temp.end());

//	fprintf(dump_file,"\nKilling Self Loops\n");
//	print_set_edges(temp);

//	temp = kill_subsumed_edges(id);   // Kill4 => Subsumed Edges
//	kill_list.insert(temp.begin(),temp.end());

//	fprintf(dump_file,"\nEntire Kill Set\n");	
//	print_set_edges(kill_list);

	#if STATS
	temp_time = stoptime();

	kill_time += temp_time;

//	fprintf(dump_file,"\nkill: Called %d times so far, Overall Time Taken: %lg, Time Taken for this Call %lg\n", kill_count, kill_time, temp_time);
	#endif
	
	return kill_list;
}	

#if 1
DVG DVG::meet(basic_block bb, DVG g2, struct cgraph_node *cnode, bool data)
{
	#if STATS
	starttime();
	#endif

	DVG g;

	set_edges elist1, elist2, elist, elist1_diff, elist2_diff, remove;

	elist1 = get_edge_list();
	elist2 = g2.get_edge_list();

	tuple< set_edges, set_edges > tt1, tt2;
	set_edges elist1_s, elist1_h, elist2_s, elist2_h, elist1_h_diff, elist2_h_diff;

	tt1 = separate_stack_heap();
	tt2 = g2.separate_stack_heap();

	elist1_s = get<0>(tt1);
	elist1_h = get<1>(tt1);

	elist2_s = get<0>(tt2);
	elist2_h = get<1>(tt2);

	set_intersection(elist1_h.begin(), elist1_h.end(), elist2_h.begin(), elist2_h.end(), inserter(elist, elist.end()));

	set_difference(elist1_h.begin(), elist1_h.end(), elist.begin(), elist.end(), inserter(elist1_h_diff, elist1_h_diff.end()));
	set_difference(elist2_h.begin(), elist2_h.end(), elist.begin(), elist.end(), inserter(elist2_h_diff, elist2_h_diff.end()));

	elist.insert(elist1_s.begin(), elist1_s.end());
	elist.insert(elist2_s.begin(), elist2_s.end());

	edge_it eit1, eit2, eit;

	Edge e1, e2;

	int x = 0, y, z, w, v = INFINITY;
	set_edges empty_edges;

	for(eit1=elist1_h_diff.begin(); eit1 != elist1_h_diff.end(); eit1++)
	{
		e1 = get_edge(*eit1);

		y = ((function_info *)(cnode->aux))->get_order_edge(*eit1);

		for(eit2=elist2_h_diff.begin(); eit2 != elist2_h_diff.end(); eit2++)
		{
			e2 = get_edge(*eit2);

			z = ((function_info *)(cnode->aux))->get_order_edge(*eit2);

			if(z > y)
			{
				w = z;
			}
			else
			{
				w = y;
			}

			if(x < w)
			{
				x = w;
			}
	
			if(v > w)
			{
				v = w;	
			}

			il il1, il2, il3, il4, il5, il6;

			if(e1.get_lhs().get_var_id() == e2.get_lhs().get_var_id() && e1.get_rhs().get_var_id() == e2.get_rhs().get_var_id())
			{
				// Indirection lists are not identical
				
				il1 = e1.get_lhs().get_ind_list();  
				il2 = e1.get_rhs().get_ind_list();  

				il3 = e2.get_lhs().get_ind_list();  
				il4 = e2.get_rhs().get_ind_list();  

				int a, b, i;

				il5 = il1.common_part(il3);
				il6 = il2.common_part(il4);

				if(il1.length() >= il3.length())
				{
					a = il1.length();
				}
				else
				{
					a = il3.length();
				}

				if(il2.length() >= il4.length())
				{
					b = il2.length();
				}
				else
				{
					b = il4.length();
				}

//				for(i = 0; i < x; i++)
				for(i = il5.length(); i < a; i++)
				{
//					il5.add_deref(NDEREF);
					il5.add_deref(FSDEREF);
				}

//				for(i = 0; i < y; i++)
				for(i = il6.length(); i < b; i++)
				{
//					il6.add_deref(NDEREF);
					il6.add_deref(FSDEREF);
				}

				Node n_l, n_r;

				n_l.set_var_id(e1.get_lhs().get_var_id());
				n_l.set_ind_list(il5);
				n_l.add_node_map();

				n_r.set_var_id(e1.get_rhs().get_var_id());
				n_r.set_ind_list(il6);
				n_r.add_node_map();

				Edge e;

				e.set_lhs(n_l);
				e.set_rhs(n_r);
				e.compute_edge_id();
	
				elist.insert(e.get_edge_id());
				
				remove.insert(*eit1);
				remove.insert(*eit2);

			}
					
		}	
	}

	set_edges elist1_rem, elist2_rem;

	set_difference(elist1_h_diff.begin(), elist1_h_diff.end(), remove.begin(), remove.end(), inserter(elist1_rem, elist1_rem.end()));
	set_difference(elist2_h_diff.begin(), elist2_h_diff.end(), remove.begin(), remove.end(), inserter(elist2_rem, elist2_rem.end()));

	elist.insert(elist2_rem.begin(), elist2_rem.end());
	elist.insert(elist1_rem.begin(), elist1_rem.end());
	
	g.add_edges(bb, elist, cnode, x, data);

	#if STATS
	temp_time = stoptime();

	meet_count++;

	meet_time += temp_time;	

//	fprintf(dump_file,"\nmeet: Called %d times so far, Overall Time Taken: %lg, Time Taken for this Call %lg\n", meet_count, meet_time, temp_time);
	#endif

	return g;
}
#endif

#if 0
DVG DVG::meet(basic_block bb, DVG g2, struct cgraph_node *cnode, bool data)
{
	#if STATS
	starttime();
	#endif

	DVG g;

	set_edges elist1, elist2, elist, elist1_diff, elist2_diff, remove;

	elist1 = get_edge_list();
	elist2 = g2.get_edge_list();

	edge_it eit1, eit2, eit;

	set_intersection(elist1.begin(), elist1.end(), elist2.begin(), elist2.end(), inserter(elist, elist.end()));
//	set_symmetric_difference(elist1.begin(), elist1.end(), elist2.begin(), elist2.end(), inserter(symm_diff, sym_diff.end()));

	set_difference(elist1.begin(), elist1.end(), elist.begin(), elist.end(), inserter(elist1_diff, elist1_diff.end()));
	set_difference(elist2.begin(), elist2.end(), elist.begin(), elist.end(), inserter(elist2_diff, elist2_diff.end()));

	#if 0
	for(eit=elist.begin(); eit != elist.end(); eit++)
	{
		elist1.erase(*eit);

		elist2.erase(*eit);
	}
	#endif

	Edge e1, e2;

	int x = 0, y, z, w, v = INFINITY;
	set_edges empty_edges;

//	for(eit1=elist1.begin(); eit1 != elist1.end(); eit1++)
	for(eit1=elist1_diff.begin(); eit1 != elist1_diff.end(); eit1++)
	{
		e1 = get_edge(*eit1);

		y = ((function_info *)(cnode->aux))->get_order_edge(*eit1);

//		for(eit2=elist2.begin(); eit2 != elist2.end(); eit2++)
		for(eit2=elist2_diff.begin(); eit2 != elist2_diff.end(); eit2++)
		{
			e2 = get_edge(*eit2);

			z = ((function_info *)(cnode->aux))->get_order_edge(*eit2);

			if(z > y)
			{
				w = z;
			}
			else
			{
				w = y;
			}

			if(x < w)
			{
				x = w;
			}
	
			if(v > w)
			{
				v = w;	
			}

			il il1, il2, il3, il4, il5, il6;

			#if 1
			if(e1.get_lhs().get_var_id() == e2.get_lhs().get_var_id() && e1.get_rhs().get_var_id() == e2.get_rhs().get_var_id())
			{
				// Indirection lists are not identical
				
				#if 0
				if(e1.is_stack_edge())
				{
					elist.insert(*eit1);
					elist.insert(*eit2);

					remove.insert(*eit1);
					remove.insert(*eit2);

					continue;
				}
				#endif
				
				il1 = e1.get_lhs().get_ind_list();  
				il2 = e1.get_rhs().get_ind_list();  

				il3 = e2.get_lhs().get_ind_list();  
				il4 = e2.get_rhs().get_ind_list();  

				int a, b, i;

				il5 = il1.common_part(il3);
				il6 = il2.common_part(il4);

				if(il1.length() >= il3.length())
				{
					a = il1.length();
				}
				else
				{
					a = il3.length();
				}

				if(il2.length() >= il4.length())
				{
					b = il2.length();
				}
				else
				{
					b = il4.length();
				}

//				for(i = 0; i < x; i++)
				for(i = il5.length(); i < a; i++)
				{
//					il5.add_deref(NDEREF);
					il5.add_deref(FSDEREF);
				}

//				for(i = 0; i < y; i++)
				for(i = il6.length(); i < b; i++)
				{
//					il6.add_deref(NDEREF);
					il6.add_deref(FSDEREF);
				}

				Node n_l, n_r;

				n_l.set_var_id(e1.get_lhs().get_var_id());
				n_l.set_ind_list(il5);
				n_l.add_node_map();

				n_r.set_var_id(e1.get_rhs().get_var_id());
				n_r.set_ind_list(il6);
				n_r.add_node_map();

				Edge e;

				e.set_lhs(n_l);
				e.set_rhs(n_r);
				e.compute_edge_id();
	
				elist.insert(e.get_edge_id());
				
				remove.insert(*eit1);
				remove.insert(*eit2);

			}
			#endif
					
		}	
	}

	set_edges elist1_rem, elist2_rem;

	set_difference(elist1_diff.begin(), elist1_diff.end(), remove.begin(), remove.end(), inserter(elist1_rem, elist1_rem.end()));
	set_difference(elist2_diff.begin(), elist2_diff.end(), remove.begin(), remove.end(), inserter(elist2_rem, elist2_rem.end()));

	#if 0
	for(eit2=remove.begin(); eit2 != remove.end(); eit2++)
	{
		elist2_rem.erase(*eit2);
		elist1_rem.erase(*eit2);
	}
	#endif

	elist.insert(elist2_rem.begin(), elist2_rem.end());
	elist.insert(elist1_rem.begin(), elist1_rem.end());
	
//	fprintf(dump_file,"\nInside meet call to add_edges\n");
	g.add_edges(bb, elist, cnode, x, data);

	#if 0
	map<unsigned int, set_edges> ord_map = ((function_info *)(cnode->aux))->get_order_map();
//	map<edge_id, unsigned int> rev_ord_map = ((function_info *)(cnode->aux))->get_rev_order_map();

	for(int j = v; j < x; j++)
	{
		ord_map[j] = empty_edges;
	}
	
	((function_info *)(cnode->aux))->set_order_map(ord_map);
	#endif

	#if STATS
	temp_time = stoptime();

	meet_count++;

	meet_time += temp_time;	

//	fprintf(dump_file,"\nmeet: Called %d times so far, Overall Time Taken: %lg, Time Taken for this Call %lg\n", meet_count, meet_time, temp_time);
	#endif

	return g;
}
#endif

// live_info APIs

live_type live_info::get_l_info()
{
	return l_info;
}

void live_info::set_l_info(live_type l)
{
	l_info = l;
}

bool live_info::get_deref()
{
	return deref;
}

void live_info::set_deref()
{
	deref = true;
}

void live_info::reset_deref()
{
	deref = false;
}

live_info live_info::copy_live_info()
{
	live_info result;

	result.set_l_info(get_l_info());

	if(get_deref())
	{
		result.set_deref();
	}
	else
	{
		result.reset_deref();
	}

	return result;
}

void live_info::print_live_info()
{
	live_type temp = get_l_info();

	 node_it it;

//	fprintf(dump_file,"\nLiveness Info\n");
	
	for(it = temp.begin(); it != temp.end(); it++)
	{
//		fprintf(dump_file,"%d\t",*it);
		fprintf(dump_file,"%d\t",*it);
//		fprintf(dump_file,"%s\t",get_var_name(*it));

//		fprintf(dump_file,"\nHellooooo\n");
	}

	fprintf(dump_file,"\n");
}

live_info live_info::meet_live(live_info l, struct cgraph_node *cnode)
{
	live_type temp1, temp2;
	live_info result;

	temp1 = get_l_info();
	temp2 = l.get_l_info();

	temp1.insert(temp2.begin(), temp2.end());

	result.set_l_info(temp1);

	if(get_deref() || l.get_deref())
	{
		result.set_deref();
	}
	else
	{
		result.reset_deref();
	}

	return result;
}

bool operator<(const live_info & l1, const live_info & l2)
{
	if(l1.l_info < l2.l_info)
		return true;
	
	return false;

}

bool operator==(const live_info & l1, const live_info & l2)
{
	if(l1.l_info == l2.l_info)
		return true;
	
	return false;

}

void live_info::generate_live_info(constraint_t con, struct cgraph_node *cnode, unsigned int cons_id, live_info lout, DVG pin)
{
	#if TRACE
//	fprintf(dump_file,"\nInside generate_live_info\n");
	#endif
	
	if(con->rhs.ptr_arith && !con->heap_alloc)
        {
                #if TRACE
                {
//                fprintf(dump_file,"\nPointer Arithmetic\n");
                }
                #endif

                con->rhs.var = 0;
                con->rhs.type = 0;
                con->rhs.offset = 0;
        }


        if(con->lhs.var == undef_id || con->lhs.var == nothing_id || con->lhs.var == escaped_id || con->lhs.var == readonly_id)
                return;

        if(con->rhs.var == nothing_id || con->rhs.var == escaped_id || con->rhs.var == readonly_id)
                return;


	live_type gen, kill, out, result;

	out = lout.get_l_info();

//	fprintf(dump_file,"\nLive Out Info\n");
//	lout.print_live_info();

	if((!unexpandable_var(con->lhs.var, con->lhs.offset) || !unexpandable_var(con->rhs.var, con->rhs.offset)) && infi_thresh < 2)
	{
//		fprintf(dump_file,"\nStatement Ignored\n");
		#if TRACE
//		fprintf(dump_file,"\nStatement Ignored\n");
		#endif
		return;
	}

	set_edges temp_edges;
	edge_it it;
	Edge e;

//	fprintf(dump_file,"\nFlow Function\n");
//	fprintf(dump_file,"\n(%d,%d,%d) -> (%d,%d, %d)\n", con->lhs.var, con->lhs.type, con->lhs.offset, con->rhs.var, con->rhs.type, con->rhs.offset);

	// 5 cases

	if(con->lhs.type == 1 && con->rhs.type == 0)
	{
//		fprintf(dump_file,"\nPoints-to Edge\n");

//		fprintf(dump_file,"\nKilling %d\n",con->lhs.var);

//		if(global_var(con->rhs.var))
		{
			gen.insert(con->rhs.var);
		}
//		fprintf(dump_file,"\nKilling %s\n",get_var_name(con->lhs.var));

		kill.insert(con->lhs.var);
	}
	else if(con->lhs.type == 1 && con->rhs.type == 1)
	{
//		fprintf(dump_file,"\nCopy Edge\n");

//		fprintf(dump_file,"\nKilling %d\n",con->lhs.var);
//		fprintf(dump_file,"\nKilling %s\n",get_var_name(con->lhs.var));

		kill.insert(con->lhs.var);

		if(out.find(con->lhs.var) != out.end() || global_var(con->lhs.var))
		{
//			fprintf(dump_file,"\nGenerating Liveness of %d\n",con->rhs.var);
//			fprintf(dump_file,"\nGenerating Liveness of %s\n",get_var_name(con->rhs.var));

			gen.insert(con->rhs.var);
		}	
	}
	else if(con->lhs.type == 1 && con->rhs.type == 2)
	{
//		fprintf(dump_file,"\nLoad Edge\n");

//		fprintf(dump_file,"\nKilling %d\n",con->lhs.var);
//		fprintf(dump_file,"\nKilling %s\n",get_var_name(con->lhs.var));

		kill.insert(con->lhs.var);

		if(out.find(con->lhs.var) != out.end() || global_var(con->lhs.var))
		{
//			fprintf(dump_file,"\nGenerating Liveness of %d\n",con->rhs.var);
//			fprintf(dump_file,"\nGenerating Liveness of %s\n",get_var_name(con->rhs.var));

			gen.insert(con->rhs.var);

			temp_edges = get<1>(pin.get_node_edge_map()[con->rhs.var]);

			for(it = temp_edges.begin(); it != temp_edges.end(); it++)
			{
				Edge e = get_edge(*it);

				if(e.get_lhs().get_ind_list().length() == 1)
				{
//					fprintf(dump_file,"\nPointee of RHS Liveness\n");

//					fprintf(dump_file,"\nGenerating Liveness of %d\n",e.get_rhs().get_var_id());
//					fprintf(dump_file,"\nGenerating Liveness of %s\n",get_var_name(e.get_rhs().get_var_id()));

					gen.insert(e.get_rhs().get_var_id());
				}
			}	
		}	
	}
	else if(con->lhs.type == 2 && con->rhs.type == 0)
	{
//		fprintf(dump_file,"\nStore-Addr Edge\n");

//		fprintf(dump_file,"\nGenerating Unconditional Liveness %d\n",con->lhs.var);
//		fprintf(dump_file,"\nGenerating Unconditional Liveness %s\n",get_var_name(con->lhs.var));

		gen.insert(con->lhs.var);

		set_edges temp_edges1 = get<1>(pin.get_node_edge_map()[con->lhs.var]);

		for(it = temp_edges1.begin(); it != temp_edges1.end(); it++)
		{
			Edge e = get_edge(*it);

			if(e.get_lhs().get_ind_list().length() == 1)
			{
				temp_edges.insert(*it);
			}
		}

//		fprintf(dump_file,"\nEdges\n");
//		print_set_edges(temp_edges);

		if(temp_edges.empty())
		{
//			fprintf(dump_file,"\nKill Everything for Monotonocity\n");

			kill.insert(out.begin(), out.end());
		}
		else if(temp_edges.size() == 1)
		{
			it = temp_edges.begin();
			Edge e = get_edge(*it);

			if(CDV.find(e.get_rhs().get_var_id()) == CDV.end())
			{
				if(!unexpandable_var(e.get_rhs().get_var_id(),con->lhs.offset))
				{
					csvarinfo_t vi;
					vi = cs_first_vi_for_offset(VEC_index(csvarinfo_t, csvarmap, e.get_rhs().get_var_id()), con->lhs.offset);

//					fprintf(dump_file,"\nKilling %d\n",vi->id);
//					fprintf(dump_file,"\nKilling %s\n",get_var_name(vi->id));

					kill.insert(vi->id);	
				}
				else
				{
//					fprintf(dump_file,"\nKilling %d\n",e.get_rhs().get_var_id());
//					fprintf(dump_file,"\nKilling %s\n",get_var_name(e.get_rhs().get_var_id()));

					kill.insert(e.get_rhs().get_var_id());
				}
			}
		}
	}
	else if(con->lhs.type == 2 && con->rhs.type == 1)
	{
//		fprintf(dump_file,"\nStore Edge\n");

//		fprintf(dump_file,"\nGenerating Unconditional Liveness %d\n",con->lhs.var);
//		fprintf(dump_file,"\nGenerating Unconditional Liveness %s\n",get_var_name(con->lhs.var));

		gen.insert(con->lhs.var);

		set_edges temp_edges1 = get<1>(pin.get_node_edge_map()[con->lhs.var]);

		for(it = temp_edges1.begin(); it != temp_edges1.end(); it++)
		{
			Edge e = get_edge(*it);

			if(e.get_lhs().get_ind_list().length() == 1)
			{
				temp_edges.insert(*it);
			}
		}

//		fprintf(dump_file,"\nEdges\n");
//		print_set_edges(temp_edges);

		if(temp_edges.empty())
		{
//			fprintf(dump_file,"\nKill Everything for Monotonocity\n");

			kill.insert(out.begin(), out.end());
		}
		else if(temp_edges.size() == 1)
		{
			it = temp_edges.begin();
			Edge e = get_edge(*it);

			if(CDV.find(e.get_rhs().get_var_id()) == CDV.end())
			{
				unsigned int pq;

				if(!unexpandable_var(e.get_rhs().get_var_id(),con->lhs.offset))
				{
					csvarinfo_t vi;
					vi = cs_first_vi_for_offset(VEC_index(csvarinfo_t, csvarmap, e.get_rhs().get_var_id()), con->lhs.offset);
					pq = vi->id;	

//					fprintf(dump_file,"\nKilling %d\n",vi->id);
//					fprintf(dump_file,"\nKilling %s\n",get_var_name(vi->id));
				}
				else
				{
					pq = e.get_rhs().get_var_id();

//					fprintf(dump_file,"\nKilling %d\n",e.get_rhs().get_var_id());
//					fprintf(dump_file,"\nKilling %s\n",get_var_name(e.get_rhs().get_var_id()));
				}

				kill.insert(pq);

				if(out.find(pq) != out.end() || global_var(pq))
				{
//					fprintf(dump_file,"\nGenerating Liveness of %d\n",con->rhs.var);
//					fprintf(dump_file,"\nGenerating Liveness of %s\n",get_var_name(con->rhs.var));

					gen.insert(con->rhs.var);
				}
			}
		}
		else
		{
			for(it = temp_edges.begin(); it != temp_edges.end(); it++)
			{
				e = get_edge(*it);
				unsigned int pq;

				if(!unexpandable_var(e.get_rhs().get_var_id(),con->lhs.offset))
				{
					csvarinfo_t vi;
					vi = cs_first_vi_for_offset(VEC_index(csvarinfo_t, csvarmap, e.get_rhs().get_var_id()), con->lhs.offset);
					pq = vi->id;	
				}
				else
				{
					pq = e.get_rhs().get_var_id();
				}
	
				if(out.find(pq) != out.end() || global_var(pq))
				{
//					fprintf(dump_file,"\nGenerating Liveness of %d\n",con->rhs.var);
//					fprintf(dump_file,"\nGenerating Liveness of %s\n",get_var_name(con->rhs.var));

					gen.insert(con->rhs.var);
					break;
				}
			}
		}	
	}

	live_type temp_result = get_l_info();

//	fprintf(dump_file,"\nKill\n");
//	print_set_vars(kill);

//	fprintf(dump_file,"\nGen\n");
//	print_set_vars(gen);

	set_difference(temp_result.begin(), temp_result.end(), kill.begin(), kill.end(), inserter(result, result.end()));

	result.insert(gen.begin(), gen.end());

	set_l_info(result);

//	fprintf(dump_file,"\nLiveness Information After Adding One Constraint\n");
//	print_live_info();
}

bool DVG::multiple_outgoing_edges(Node n)
{
	var_incom_out var_map = get_node_edge_map();

	set_edges temp_edges = get<1>(var_map[n.get_var_id()]);

	edge_it it;
	Edge e;

	if(temp_edges.size() > 1)
	{

		#if 1	
		for(it = temp_edges.begin(); it != temp_edges.end(); it++)
		{
			e = get_edge(*it);

			if(CDV.find(e.get_lhs().get_var_id()) != CDV.end())
			{
				return true;
			}		
		}
		#endif

//		return true;	
	}

	return false;
}

// Accessing Global Data Structures node_map

Node get_node(node_id id)
{
	vec_nodes temp = node_map[get<0>(id)][get<1>(id)];

	return temp[get<2>(id)];
}

Edge get_edge(edge_id id)
{
	Edge e;

	Node lhs = get_node(get<0>(id));

	Node rhs = get_node(get<1>(id));

	e.set_lhs(lhs);
	e.set_rhs(rhs);
	e.compute_edge_id();

	return e;	
}

void print_set_edges(set_edges s)
{
	edge_it eit;
	Edge e;

	for(eit=s.begin(); eit != s.end(); eit++)
	{
		e = get_edge(*eit);

		e.print_edge();
	}
}

void print_edge_id(edge_id id)
{
	print_node_id(get<0>(id));
	print_node_id(get<1>(id));

//	Edge e = get_edge(id);

//	e.print_edge();
}

void print_node_id(node_id id)
{
//	fprintf(dump_file,"\nNode ID\n");

	fprintf(dump_file,"(%d, %d, %d) ",get<0>(id),get<1>(id),get<2>(id));

//	Node n = get_node(id);

//	n.print_node();
}

void DVG::print_node_edge_map()
{
	var_list nodes = get_node_list();
	var_incom_out nodes_edges = get_node_edge_map();

	node_it nit;

	tuple< set_edges, set_edges > temp;
	edge_it eit;
	set_edges temp_edges;
	Edge e;	

	fprintf(dump_file,"\nPrinting node-edge-map\n");

	for(nit = nodes.begin(); nit != nodes.end(); nit++)
	{
		temp = nodes_edges[*nit];

		temp_edges = get<1>(temp);

		eit = temp_edges.begin();

		for(eit; eit != temp_edges.end(); eit++)
		{
			e = get_edge(*eit);

			e.print_edge();
		}
	}
}

bool check_array(unsigned int var)
{

//	fprintf(dump_file,"\nInside check_array\n");

        if(CDV.find(var) != CDV.end())
        {
//              fprintf(dump_file,"\nCDV\n");
                var = var - 1;
        }

//	fprintf(dump_file,"\nVar %s\n",get_var_name(var));

        tree u = VEC_index(csvarinfo_t,csvarmap,var)->decl;

        if(var == undef_id || var == nothing_id || var == escaped_id || var == readonly_id)
                return false;

        if(TREE_CODE(TREE_TYPE(u)) == ARRAY_TYPE || TREE_CODE(TREE_TYPE(u)) == ARRAY_REF)
        {
                #if TRACE
                {
//                fprintf(dump_file,"\nArray\n");
                }
                #endif
                return true;
        }

        return false;
}

void print_set_nodes(set<Node> s)
{
	set<Node>::iterator it;
	Node n;

	for(it = s.begin(); it != s.end(); it++)
	{
		n = *it;

		n.print_node();	
	}
}

void print_set_node_ids(set_nodes s)
{
	Node_it it;
	Node n;

	for(it = s.begin(); it != s.end(); it++)
	{
		n = get_node(*it);

		n.print_node();
	}
}

void print_set_vars(live_type lt)
{
	node_it it;

	for(it = lt.begin(); it != lt.end(); it++)
	{
		fprintf(dump_file,"%s\t", get_var_name(*it));
	}
	fprintf(dump_file,"\n");
}

set_edges create_boundary_edges(unsigned int var)
{
	set_edges elist;
	Node lhs, rhs;

	if(var <= 3 || CDV.find(var) != CDV.end())
	{
		return elist;
	}	

	il il1, il2;

	il1.add_deref(-1); // il for x->x' edge

	for(int i = 0; i < infi_thresh; i++)
	{
		il2.add_deref(-1);
	}	
	il2.set_infinity(); // il for x'->x' edge
	
	lhs.set_var_id(var);	
	lhs.set_ind_list(il1);
	lhs.add_node_map();

	rhs.set_var_id(var+1);
	rhs.set_ind_list(il1);
	rhs.add_node_map();

	Edge e(lhs,rhs);

	elist.insert(e.get_edge_id());

	lhs.set_var_id(var+1);
	lhs.set_ind_list(il1);
	lhs.add_node_map();

	rhs.set_var_id(var+1);
	rhs.set_ind_list(il2);
	rhs.add_node_map();

	Edge e_loop(lhs,rhs);

	elist.insert(e_loop.get_edge_id());

	return elist;
}

void push_bound_info_callers(struct cgraph_node *cnode, set_edges bound_edges)
{
	struct cgraph_edge *edge;

	struct cgraph_node *node;
	basic_block startbb;
	DVG g;

//	fprintf(dump_file,"\nCallers of %s\n",cgraph_node_name(cnode));

	for (edge = cnode->callers; edge; edge = edge->next_caller)
	{
		node = edge->caller;

//		fprintf(dump_file,"\nCaller %s\n",cgraph_node_name(node));

		startbb = start_bb_of_fn(node);

		g = ((block_information *)(startbb->aux))->get_points_in();

//		g.add_edges(bound_edges, node, 0, false);			

		((block_information *)(startbb->aux))->set_points_in(g);
	}

//	fprintf(dump_file,"\nHiiii\n");
}
