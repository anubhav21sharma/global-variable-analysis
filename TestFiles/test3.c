#include <stdio.h>
int ga,gb,gc,gd;
int b,c,d;
//int g()
//{
//	int a;
//	a = d;
//	g();
//	return a;
//}
//int f()
//{
//	a=0;
//	if(a>=2)
//		a=b;
//	else
//		b=c;
//	g();
//	return a;
//}
int main ()
{
	int a;
	a = b+2;
	b = a*b;
	//printf("a:%d\n",a);
	return a;
}


//TODO:
//1. Iterate over call graph.
//2. Find direct/indirect accesses.
//3. Handle conditional,function call,switch, return statements.
