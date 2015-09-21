#include <stdio.h>
int a,b,c,d;
int g()
{
	int a;
	a = d;
	g();
	return a;
}
int f()
{	
	a=0;
	if(a>=2)
		a=b;
	else
		b=c;
	g();
	return a;
}
int main ()
{
	int a;
	a = f();
	printf("a:%d\n",a);
	return 0;
}
