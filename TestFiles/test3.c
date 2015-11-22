#include <stdio.h>
int ga, gb, gc, gd;
int k();
int g() {
	int ga;
	ga = gd;
	g();
	return ga;
}
int f() {
	k();
	if (ga >= 2)
		ga = gb;
	else
		gb = gc;
	g();
	return ga;
}

int k() {
	int ga;
	ga = gd;
	k();
	return gb;
}

int main() {
	return k();
}


