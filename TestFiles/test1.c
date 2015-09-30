#include <stdio.h>

int ga,gb,gc;

int fn1(int i)
{
	printf ("\n in fn1 : %d", i);
}

int fn2(int i)
{
	printf ("\n in fn2 : %d", i);
	fn1 (5);
}


int main()
{
	int n, a, b, c, d;
	a = b + c;
	a = a * d;
	if (n)
		n = n - a;
	else
		n = n + a;

	fn1 (n-6);
	fn2 (n+7);
}

