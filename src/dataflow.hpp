#ifndef DATAFLOW_H
#define DATAFLOW_H

#include<algorithm>
#include "parser.hpp"
#include<utility>
#include<iostream>
#include<set>
#include<map>
#include<list>
#include<vector>
#include <tr1/tuple>
#include<sys/time.h>
#include<time.h>
#define INFINITY 999
#define NDEREF -1
#define FSDEREF -2
#define LR 1
#define LL 2

#define TRACE 0
#define STATS 0
#define TIME 0

#define OPTION 0

#if OPTION == 1
	#define LIVENESS 1
	#define FCOMP 1
	#define DFVSFFALL 1
#elif OPTION == 2
	#define LIVENESS 1
	#define FCOMP 1
	#define DFVSFFCALL 1
#elif OPTION == 3
	#define LIVENESS 1
	#define FCOMP 1
	#define DFVSFFCALLBB 1
#elif OPTION == 4
	#define LIVENESS 1
	#define INCFCOMP 1
	#define DFVSFFALL 1
#elif OPTION == 5
	#define LIVENESS 1
	#define INCFCOMP 1
	#define DFVSFFCALL 1
#elif OPTION == 6
	#define LIVENESS 1
	#define INCFCOMP 1
	#define DFVSFFCALLBB 1
#elif OPTION == 7
	#define FCOMP 1
	#define DFVSFFALL 1
#elif OPTION == 8
	#define FCOMP 1
	#define DFVSFFCALL 1
#elif OPTION == 9
	#define FCOMP 1
	#define DFVSFFCALLBB 1
#elif OPTION == 10
	#define INCFCOMP 1
	#define DFVSFFALL 1
#elif OPTION == 11
	#define INCFCOMP 1
	#define DFVSFFCALL 1
#elif OPTION == 12
	#define INCFCOMP 1
	#define DFVSFFCALLBB 1
#endif

using namespace std;
using namespace std::tr1;

// Counts for statistics

extern unsigned int meet_count;
extern unsigned int gcomp_count;
extern unsigned int add_edge_count;
extern unsigned int delete_edge_count;
extern unsigned int infinity_edge_count;
extern unsigned int constraint_edge_count;

extern unsigned int edge_comp_count;
extern unsigned int kill_count;
extern unsigned int add_edges_func_count;
extern unsigned int remove_edges_func_count;
extern unsigned int func_comp_count;

extern unsigned int ptr_arith_count_stack;
extern unsigned int ptr_arith_count_heap;

extern double edge_comp_time;
extern double kill_time;
extern double add_edges_time;
extern double remove_edges_time;
extern double meet_time;
extern double func_comp_time;

//extern double temp_time;

extern struct timeval t_start, t_end, result;

extern clock_t start, end;

//==================================================================================
extern unsigned int max_size;
extern int new_field;

typedef vector<int> il_type;

extern unsigned int infi_thresh;
extern unsigned int f_insens_thresh;

class il
{
	il_type deref_list;
	bool infi;

	public:
		il(){infi = false;};

		il_type get_deref_list();
		void set_deref_list(il_type);

		void add_deref(int x);
		il pop_deref_list();
		int first_ele_deref_list();

		void set_infinity();
		bool is_infinity();

		il append(il);
		il get_remainder(il);
		il common_part(il);

		bool is_prefix(il);
		bool is_eq(il);

		unsigned int length();	

		void print_il();

		friend bool operator<(const il & i1, const il & i2);
                friend bool operator==(const il & i1, const il & i2);

};

typedef il_type::iterator il_it;

typedef tuple< unsigned int, unsigned int, unsigned int > node_id;
typedef tuple< node_id, node_id > edge_id;

class Node
{
	unsigned int var_id;
	il ind_list;

	node_id nid;
	

	public:
		Node(){};

		Node(struct constraint_expr, int) ;

		unsigned int get_var_id();
		void set_var_id(unsigned int);
	
		il get_ind_list();
		void set_ind_list(il);

		node_id get_node_id();
		void set_node_id(node_id);

		friend bool operator<(const Node & n1, const Node & n2);
                friend bool operator==(const Node & n1, const Node & n2);

		bool sim(Node);
		bool node_eq(Node);
		bool sim_summ(Node);
		bool node_eq_summ(Node);

		Node construct_new_node(edge_id, int);

		void add_node_map();

		Node con_dep();

		void print_node();
		Node get_structure_node(int);

		bool check_if_temp();
};

extern Node undef_node;

typedef set< edge_id > set_edges;
typedef set< node_id > set_nodes;

typedef set< unsigned int > var_list;

typedef map< unsigned int, tuple< set_edges, set_edges > > var_incom_out; // 1st entry in tuple is incoming edges and 2nd entry corresponds to outgoing edges

typedef vector<Node> vec_nodes;

typedef map< unsigned int, vec_nodes > sec_map;

extern map< unsigned int, sec_map > node_map;

typedef set<unsigned int> live_type;

class Edge
{
	Node lhs, rhs;
	edge_id eid;

	public:
		Edge(){};
	
		Edge(Node, Node);
	
		Node get_lhs();
		Node get_rhs();

		void set_lhs(Node);
		void set_rhs(Node);

		edge_id get_edge_id();
		void set_edge_id(edge_id);
		void compute_edge_id();

		friend bool operator<(const Edge & e1, const Edge & e2);
                friend bool operator==(const Edge & e1, const Edge & e2);

		bool is_infinity();
		bool can_compose();

		bool is_self_loop();
		bool is_stack_edge();
		bool is_boundary_edge();
		bool is_con_dep_edge();

		void print_edge();
};

class DVG
{
	var_list node_list;

	set_edges edge_list;

	var_incom_out node_edge_map;
	
	bool top;

	public:
		DVG(){top = true;};
		

		bool is_top();
		void set_top();
		void reset_top();

		var_list get_node_list();
		set_edges get_edge_list();
		var_incom_out get_node_edge_map();

		void set_node_list(var_list);
		void set_edge_list(set_edges);
		void set_node_edge_map(var_incom_out);	

		friend bool operator<(const DVG & g1, const DVG & g2);
                friend bool operator==(const DVG & g1, const DVG & g2);

		set_edges compat_edges(Node, bool, struct cgraph_node *);

		set_nodes compose(node_id, int, struct cgraph_node *);

//		set_edges new_edges(edge_id);
		set_edges edge_comp(edge_id, struct cgraph_node *);

		set_nodes single_composition(set_nodes, int, struct cgraph_node *);

		set_nodes trans(set_nodes, int, struct cgraph_node *);

		set_edges cross_product(set_nodes, set_nodes);

		set_edges kill_edges(Node, struct cgraph_node *, DVG);

		set_nodes lhs_alias(set_edges, edge_id, struct cgraph_node *);

		set_edges strong_update(set_edges, edge_id, struct cgraph_node *, DVG);

		set_edges isl(Node p, struct cgraph_node *);
		set_edges gsl(Node, struct cgraph_node *);
		set_edges kill_self_loop(set_edges, edge_id, struct cgraph_node *);

		set_edges subsumed_edges(edge_id);

		DVG copy_dvg();
		void print_dvg();
		void generate_graph(basic_block, constraint_t con, struct cgraph_node *cnode, unsigned int cons_id);
		void func_comp(basic_block, Edge, struct cgraph_node *, unsigned int, DVG, struct cgraph_node *, bool);

		DVG meet(basic_block, DVG, struct cgraph_node *cnode, bool);
		bool multiple_outgoing_edges(Node);

		void add_edges(basic_block, set_edges, struct cgraph_node *, unsigned int, bool);
		void remove_edges(basic_block, set_edges, struct cgraph_node *, bool);
		void add_edges_fi_dvg(set_edges, struct cgraph_node *);
		void remove_edges_fi_dvg(set_edges, struct cgraph_node *);

		set_edges update_gen(set_edges);

		set_edges kill_subsumed_edges(edge_id);
		set_edges kill_subsumed_edges_from_list(set_edges, edge_id);
		set_edges kill(set_edges, edge_id, struct cgraph_node *, DVG);

		void print_node_edge_map();

		bool weaker(DVG, struct cgraph_node *);
		tuple< set_edges, set_edges > separate_stack_heap();
};

class live_info
{
	private:
		live_type l_info;
		bool deref;

	public:
		live_info() {deref = false;};
	
		bool get_deref();
		void set_deref();
		void reset_deref();

		live_type get_l_info();
		void set_l_info(live_type);

		live_info copy_live_info();
		live_info meet_live(live_info, struct cgraph_node *);

		void print_live_info();

		friend bool operator<(const live_info & l1, const live_info & l2);
                friend bool operator==(const live_info & l1, const live_info & l2);

		void generate_live_info(constraint_t, struct cgraph_node *cnode, unsigned int, live_info, DVG);
};

typedef set_edges::iterator edge_it;
typedef var_list::iterator node_it;
typedef vec_nodes::iterator nodes_it;
typedef var_incom_out::iterator node_edge_it;
typedef set_nodes::iterator Node_it;

// Accessing Global Data Structures such as node_map

Node get_node(node_id);
Edge get_edge(edge_id);
void print_set_edges(set_edges);
void print_edge_id(edge_id);
void print_node_id(node_id);
bool check_array(unsigned int);
void print_set_nodes(set<Node>);	
void print_set_node_ids(set_nodes);	
void starttime();
double stoptime();
void print_set_vars(live_type);
set_edges create_boundary_edges(unsigned int);
void push_bound_info_callers(struct cgraph_node *, set_edges);

struct cnode_cmp
{
	bool operator()(struct cgraph_node * n1, struct cgraph_node * n2) 
	{
		if(n1->order < n2->order)
			return true;

		return false;
	}
};

typedef list< struct cgraph_node * > set_cnodes;

extern map< struct cgraph_node *, set_cnodes > map_scc;

#endif
