#include <stdio.h>
int c;
void f1(int b)
{
   int a=3;
   b = 2;
   a = a+b;
   c = a + 3;
}
int main ()
{
	int a,b = 2,d;
	a = 10;
	while(a < 50)
	{
		a = a+b;
		d = d+a;
	}
	b=3;
	f1(d);
	return 0;
}
