#include<algorithm>
#include<iostream>
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
#include<set>
#include<map>
#include<vector>
#include<cstdlib>
#include<utility>
#include<sys/time.h>
#include "parser.hpp"

using namespace std;

typedef set<int> Pointee_Set;

class PSet		//class for Pointee set
{
	Pointee_Set st;
	int sum;
	public:
		PSet()
		{
			sum = 0;
		}
		void set_st(Pointee_Set);
		Pointee_Set get_st();
		void insert_into_pointee_set(int);
		int displayset();
		bool var_is_a_pointee(int);
		bool union_of_pointee_sets(PSet);
};

class Allptsinfo	//class for poits-to graph
{
	int constraint_of_type_1; // x = &y
	int constraint_of_type_2; // x = y
	int constraint_of_type_3; // x = *y
	int constraint_of_type_4; // *x = y
	int constraint_of_type_5; // *x = &y
	double time_of_constraint_1;
	double time_of_constraint_2;
	double time_of_constraint_3;
	double time_of_constraint_4;
	double time_of_constraint_5;
	int calls_to_constraint_1;
	int calls_to_constraint_2;
	int calls_to_constraint_3;
	int calls_to_constraint_4;
	int calls_to_constraint_5;
	int failed_constraints;	 //counter for constraints that were not processed
	public:
	map<int,PSet> allptinfo;
		Allptsinfo()
		{
			constraint_of_type_1 = 0;
			constraint_of_type_2 = 0;
			constraint_of_type_3 = 0;
			constraint_of_type_4 = 0;
			constraint_of_type_5 = 0;
			failed_constraints = 0;
			time_of_constraint_1 = 0.0;
			time_of_constraint_2 = 0.0;
			time_of_constraint_3 = 0.0;
			time_of_constraint_4 = 0.0;
			time_of_constraint_5 = 0.0;
			calls_to_constraint_1 = 0;
			calls_to_constraint_2 = 0;
			calls_to_constraint_3 = 0;
			calls_to_constraint_4 = 0;
			calls_to_constraint_5 = 0;
		}
		// Functions on Points to Map
		PSet get_pointee_set_object(int);

		/************/
		void Display_Map(int); //Accepts total number of iterations as an input parameter
		/***********/
		void Insert_Map(int,PSet);

		void print_failed_constraints();

		//Points to Graph evaluation function
		bool Process_Input (int, int, int, int);

};

class statistics
{
	double time;
	unsigned int calls;
	public:
	    	statistics ()
		{              
			time = 0.0;
			calls = 0;
		}
		double get_time();
		void set_time(double);
		int get_calls();
		void set_calls(int);
	    	void print ();
		void start_time(struct timeval &start);
		void stop_time(struct timeval start);
};

	
