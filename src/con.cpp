#include "con.hpp"

using namespace std;


auxiliary::auxiliary(int a, bool b)
{
index=a;
is_alias=b;
order = false;
}

int auxiliary::get_int()
{
return index;
}

bool auxiliary::get_bool()
{
return is_alias;
}


bool auxiliary::is_ordered()
{
return order;
}


void auxiliary::set_order()
{
	order = true;
}

void constraint_list::push(int id, bool b)
{
auxiliary a(id,b);
conlist.push_back(a);
}

it constraint_list::begin()
{
return conlist.begin();
}

it constraint_list::end()
{
return conlist.end();
}

rit constraint_list::rbegin()
{
return conlist.rbegin();
}

rit constraint_list::rend()
{
return conlist.rend();
}

bool constraint_list::empty()
{
return conlist.empty();
}

auxiliary & constraint_list::front()
{
return conlist.front();
}

auxiliary & constraint_list::back()
{
return conlist.back();
}

unsigned int constraint_list::size()
{
	return conlist.size();
}
////////////////////////////////////////////////////

