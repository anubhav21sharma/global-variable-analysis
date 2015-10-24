#include "block_information.hpp"
//#include "cgraph_node.hpp"

block_information::block_information(struct cgraph_node * f) {
	node = f;
	call_block = false;
	return_block = false;
	start_block = false;
	end_block = false;
	linitialized = 1;
	pinitialized = 1;
	dinitialized = 1;
}

constraint_list & block_information::get_list() {
	return cons;
}

struct cgraph_node * block_information::get_cfun() {
	return node;
}

DVG block_information::get_summ() {
	return summ;
}

void block_information::set_summ(DVG g) {
	summ = g;
}

DVG block_information::get_points_in() {
	return points_in;
}

DVG block_information::get_points_out() {
	return points_out;
}

void block_information::set_points_in(DVG g) {
	points_in = g;
}

void block_information::set_points_out(DVG g) {
	points_out = g;
}

DVG block_information::get_d_in() {
	return d_in;
}

DVG block_information::get_d_out() {
	return d_out;
}

void block_information::set_d_in(DVG g) {
	d_in = g;
}

void block_information::set_d_out(DVG g) {
	d_out = g;
}

live_info block_information::get_live_in() {
	return live_in;
}

live_info block_information::get_live_out() {
	return live_out;
}

void block_information::set_live_in(live_info l) {
	live_in = l;
}

void block_information::set_live_out(live_info l) {
	live_out = l;
}

