#include "Points_to4.hpp"

Pointee_Set PSet::get_st() {
	return st;
}

void PSet::set_st(Pointee_Set s1) {
	st = s1;
}

bool PSet::union_of_pointee_sets(PSet ob1) {
	Pointee_Set old_set, temp_set, new_set;
	old_set = get_st();
	temp_set = old_set;
	new_set = ob1.get_st();

	old_set.insert(new_set.begin(), new_set.end());
	set_st(old_set);

	if (old_set == temp_set)
		return false;
	else
		return true;
}

void PSet::insert_into_pointee_set(int s1) {
	st.insert(s1);
}

int PSet::displayset() {
	Pointee_Set::iterator it;
	int cnt = 0;
	for (it = st.begin(); it != st.end(); it++) {
		csvarinfo_t var = VEC_index(csvarinfo_t, csvarmap, *it);
		//cout<<(*it)<<endl;
		fprintf(dump_file, "%s(%d),", var->name, (*it));
#if PT_STATS						//use of PT_STATS macro
		cnt++;
		sum=sum+cnt;
#endif
	}
	return sum;
}

bool PSet::var_is_a_pointee(int s2) {
	Pointee_Set::iterator it;

	it = st.find(s2);
	if (it != st.end())
		return true;
	return false;
}

PSet Allptsinfo::get_pointee_set_object(int in) {
	return allptinfo[in];
}

void Allptsinfo::Display_Map(int total_no_of_iterations) {
	map<int, PSet>::iterator it;
	int total_no_of_nodes_in_graph = 0;
	int avg_pointee_sets = 0;
	int sum_of_all_pointees;
	for (it = allptinfo.begin(); it != allptinfo.end(); it++) {
		int pointer_id = it->first;
		csvarinfo_t pointer = VEC_index(csvarinfo_t, csvarmap, pointer_id);
		PSet ob_pset = it->second;
		//cout << "Value: " << var << ":" ;
		fprintf(dump_file, "\n<%s(%d),{", pointer->name, pointer_id);
		total_no_of_nodes_in_graph++;
		sum_of_all_pointees = ob_pset.displayset();
		fprintf(dump_file, "}>");
	}
#if 0
	fprintf(dump_file, "\n Total no. of nodes in the graph   : %d \n", total_no_of_nodes_in_graph);
#if PT_STATS
	avg_pointee_sets = sum_of_all_pointees/total_no_of_nodes_in_graph;
	fprintf(dump_file, "\n Average pointees in pointee sets   : %d \n",avg_pointee_sets );

	//Statistics for constraint x = &y
	fprintf(dump_file, "\n\n No. of constraints of type x=&y   : %d ", constraint_of_type_1/total_no_of_iterations);
	fprintf(dump_file, "\n Time required for constraint x=&y : %f microseconds", time_of_constraint_1);

	//Statistics for constraint x = y
	fprintf(dump_file, "\n\n No. of constraints of type x=y    : %d ", constraint_of_type_2/total_no_of_iterations);
	fprintf(dump_file, "\n Time required for constraint x=y  : %f microseconds", time_of_constraint_2);

	//Statistics for constraint x = *y
	fprintf(dump_file, "\n\n No. of constraints of type x=*y   : %d ", constraint_of_type_3/total_no_of_iterations);
	fprintf(dump_file, "\n Time required for constraint x=*y : %f microseconds", time_of_constraint_3);

	//Statistics for constraint *x = y
	fprintf(dump_file, "\n\n No. of constraints of type *x=y   : %d ", constraint_of_type_4/total_no_of_iterations);
	fprintf(dump_file, "\n Time required for constraint *x=y : %f microseconds", time_of_constraint_4);

	//Statistics for constraint *x = &y
	fprintf(dump_file, "\n\n No. of constraints of type *x=&y  : %d ", constraint_of_type_5/total_no_of_iterations);
	fprintf(dump_file, "\n Time required for constraint *x=&y : %f microseconds", time_of_constraint_5);
#endif
	cout<<endl;
#endif
}

void Allptsinfo::Insert_Map(int i, PSet ob) {
	allptinfo.insert(pair<int, PSet>(i, ob));
}

bool Allptsinfo::Process_Input(int lvar, int lop, int rvar, int rop) {
#if PT_TIME
	struct timeval start,stop;
#endif
	bool status = false;
	if ((lop == 1) && (rop == 0))		//x=&y
	{
#if PT_STATS
		constraint_of_type_1++;
		statistics c1_stats;
		c1_stats.start_time(start);
#endif
		PSet obj_pts_lhs, obj_pts_rhs, obj_def_ptrs, obj_pts_new;
		Pointee_Set pts_rhs, pts_lhs, new_pts, def_ptrs_set;
		obj_pts_lhs = get_pointee_set_object(lvar);
		status = obj_pts_lhs.var_is_a_pointee(rvar);
		if (!status) 	// rvar not found in the pointee set of lvar 
		{
			obj_pts_lhs.insert_into_pointee_set(rvar);
			allptinfo[lvar] = obj_pts_lhs;
			//fprintf(dump_file,"\n New iteration required by constraint x=&y");
			return true;
		}
#if PT_STATS
		c1_stats.stop_time(start);
		time_of_constraint_1 += c1_stats.get_time();
#endif
	}

	else if ((lop == 1) && (rop == 1))		//x=y
	{
#if PT_STATS
		constraint_of_type_2++;
		statistics c2_stats;
		c2_stats.start_time(start);
#endif
		PSet obj_pts_lhs, obj_pts_rhs, obj_def_ptrs, obj_pts_new;
		Pointee_Set pts_rhs, pts_lhs, new_pts, def_ptrs_set;
		obj_pts_lhs = get_pointee_set_object(lvar);
		obj_pts_rhs = get_pointee_set_object(rvar);
		status = obj_pts_lhs.union_of_pointee_sets(obj_pts_rhs);

		if (status)	// the pointee set of lvar has changed
		{
			allptinfo[lvar] = obj_pts_lhs;
			//fprintf(dump_file,"\n New iteration required by constraint x=y");
			return true;
		}
#if PT_STATS
		c2_stats.stop_time(start);
		time_of_constraint_2 += c2_stats.get_time();
#endif

	}

	else if ((lop == 1) && (rop == 2))		//x=*y
	{
#if PT_STATS		
		constraint_of_type_3++;
		statistics c3_stats;
		c3_stats.start_time(start);
#endif
		PSet obj_pts_lhs, obj_pts_rhs, obj_def_ptrs, obj_pts_new;
		Pointee_Set pts_rhs, pts_lhs, new_pts, def_ptrs_set;
		Pointee_Set::iterator it;
		obj_pts_rhs = allptinfo[rvar];
		pts_rhs = obj_pts_rhs.get_st();
		if (pts_rhs.size() == 0)
			return false;
		for (it = pts_rhs.begin(); it != pts_rhs.end(); it++) {
			obj_def_ptrs = get_pointee_set_object(*it);
			def_ptrs_set = obj_def_ptrs.get_st();
			new_pts.insert(def_ptrs_set.begin(), def_ptrs_set.end());
		}

		obj_pts_new.set_st(new_pts);
		obj_pts_lhs = allptinfo[lvar];

		status = obj_pts_lhs.union_of_pointee_sets(obj_pts_new);

		if (status) 	// pointee set of lvar has changed
		{
			allptinfo[lvar] = obj_pts_lhs;
			//fprintf(dump_file,"\n New iteration required by constraint x=*y ");
			return true;
		}
#if PT_STATS
		c3_stats.stop_time(start);
		time_of_constraint_3 += c3_stats.get_time();
#endif
	} else if ((lop == 2) && (rop == 1))		//*x=y
	{
#if PT_STATS		
		constraint_of_type_4++;
		statistics c4_stats;
		c4_stats.start_time(start);
#endif
		PSet obj_pts_lhs, obj_pts_rhs, obj_def_ptrs;
		Pointee_Set pts_rhs, pts_lhs, new_pts, def_ptrs_set;
		Pointee_Set::iterator it;
		obj_pts_lhs = allptinfo[lvar];
		pts_lhs = obj_pts_lhs.get_st();
		obj_pts_rhs = allptinfo[rvar];
		pts_rhs = obj_pts_rhs.get_st();
		if (pts_lhs.size() == 0)
			return false;
		for (it = pts_lhs.begin(); it != pts_lhs.end(); it++) {
			PSet obj_pts_new;
			Pointee_Set pts_new;

			obj_def_ptrs = get_pointee_set_object(*it);
			def_ptrs_set = obj_def_ptrs.get_st();

			status = status || obj_def_ptrs.union_of_pointee_sets(obj_pts_rhs);

			pts_new = obj_def_ptrs.get_st();
			obj_pts_new.set_st(pts_new);
			if (status) {
				allptinfo[*it] = obj_pts_new;
				//fprintf(dump_file,"\n New iteration required by constraint *x=y");
			}
		}
		if (status)
			return true;
#if PT_STATS
		c4_stats.stop_time(start);
		time_of_constraint_4 += c4_stats.get_time();
#endif	
	} else if ((lop == 2) && (rop == 0))		//*x=&y
	{
#if PT_STATS		
		constraint_of_type_5++;
		statistics c5_stats;
		c5_stats.start_time(start);
#endif
		PSet obj_pts_lhs, obj_pts_rhs, obj_def_ptrs, obj_pts_new;
		Pointee_Set pts_rhs, pts_lhs, new_pts, def_ptrs_set;
		Pointee_Set::iterator it;
		obj_pts_lhs = allptinfo[lvar];
		pts_lhs = obj_pts_lhs.get_st();
#if PT_STATS
		//obj_pts_lhs.displayset ();
		//fprintf(dump_file,"*x=&y lhs size = %d\n",pts_lhs.size());
#endif
		if (pts_lhs.size() == 0)
			return false;
		for (it = pts_lhs.begin(); it != pts_lhs.end(); it++) {
			bool temp = false;
			obj_def_ptrs = get_pointee_set_object(*it);
			def_ptrs_set = obj_def_ptrs.get_st();
			temp = obj_def_ptrs.var_is_a_pointee(rvar);
			//fprintf(dump_file,"temp = %d \n",temp);
			status = status || temp;
			obj_pts_new.set_st(def_ptrs_set);
#if PT_TEST
			//fprintf (dump_file, "\nid=%d (status=%d) points to", *it, status);
			//obj_def_ptrs.displayset ();
			//fprintf (dump_file, "\n");
#endif
			if (!status) {
				obj_pts_new.insert_into_pointee_set(rvar);
				fprintf(dump_file, "pts new size = %d \n", obj_pts_new.get_st().size());
				allptinfo[*it] = obj_pts_new;
				//fprintf(dump_file,"\n New iteration required by constraint *x=&y");
			}

		}
		if (!status)
			return true;
#if PT_STATS
		c5_stats.stop_time(start);
		time_of_constraint_5 += c5_stats.get_time();
#endif				
	} else if ((lop == 2) && (rop == 2))		// *x=*y
	{
		PSet obj_pts_lhs, obj_pts_rhs, obj_def_ptrs_lhs, obj_def_ptrs_rhs, obj_pts_new_rhs;
		Pointee_Set pts_rhs, pts_lhs, new_pts_rhs, def_ptrs_set_lhs, def_ptrs_set_rhs;
		Pointee_Set::iterator it;

		obj_pts_rhs = allptinfo[rvar];
		pts_rhs = obj_pts_rhs.get_st();
		obj_pts_lhs = allptinfo[lvar];
		pts_lhs = obj_pts_lhs.get_st();
#if PT_TEST
		//fprintf (dump_file, "\nx = ");
		//obj_pts_lhs.displayset ();
#endif
		if (pts_rhs.size() == 0 or pts_lhs.size() == 0)
			return false;
		for (it = pts_rhs.begin(); it != pts_rhs.end(); it++) {
			obj_def_ptrs_rhs = get_pointee_set_object(*it);
			def_ptrs_set_rhs = obj_def_ptrs_rhs.get_st();
			new_pts_rhs.insert(def_ptrs_set_rhs.begin(), def_ptrs_set_rhs.end());
		}
		obj_pts_new_rhs.set_st(new_pts_rhs);
#if PT_TEST
		//fprintf (dump_file, "\n*y = ");
		//obj_pts_new_rhs.displayset ();
#endif	
		for (it = pts_lhs.begin(); it != pts_lhs.end(); it++) {
			PSet obj_pts_new_lhs;
			Pointee_Set pts_new_lhs;

			obj_def_ptrs_lhs = get_pointee_set_object(*it);
#if PT_TEST
			//fprintf (dump_file, "\nold *x = ");
			//obj_def_ptrs_lhs.displayset ();
#endif
			status = status || obj_def_ptrs_lhs.union_of_pointee_sets(obj_pts_new_rhs);

			pts_new_lhs = obj_def_ptrs_lhs.get_st();
			obj_pts_new_lhs.set_st(pts_new_lhs);
#if PT_TEST
			//fprintf (dump_file, "\nnew *x = ");
			//obj_pts_new_lhs.displayset ();
#endif
			if (status) {
				allptinfo[*it] = obj_pts_new_lhs;
#if PT_TEST
				//fprintf (dump_file, "\n*it=%d points to ", *it);
				//obj_pts_new_lhs.displayset ();
				//fprintf(dump_file,"\n New iteration required by constraint *x=*y");
#endif
			}
		}
		if (status)
			return true;
	}

	else {
		//gcc_assert(0);
		failed_constraints++;
		//cerr()
	}

	return false;
}
void Allptsinfo::print_failed_constraints() {
	if (failed_constraints)
		fprintf(dump_file, "\n\n Failed constraints =%d \n", failed_constraints);
}

void statistics::print() {
	fprintf(dump_file, " Time : %f seconds / No. of calls : %u\n", time, calls);
}

double statistics::get_time() {
	return time;
}

int statistics::get_calls() {
	return calls;
}

void statistics::set_time(double t) {
	time = t;
}

void statistics::set_calls(int c) {
	calls = c;
}

void statistics::start_time(struct timeval &start) {
	gettimeofday(&start, NULL);
}

void statistics::stop_time(struct timeval start) {
	float t;
	struct timeval stop;
	gettimeofday(&stop, NULL);

	t = (double) (stop.tv_sec - start.tv_sec) * 1000000 + (double) (stop.tv_usec - start.tv_usec);

	time += t;
	calls++;
}
