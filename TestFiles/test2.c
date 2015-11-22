#include <stdio.h>

int xx;
int *pxx;

void f();
void g();
void h();
void i();
int k();
void j();
void x();
void y(int);

void f() {
	g();
	h();
}

void g() {
	i();
	j();
}

void i() {
}

void j() {
	j();
}

void h() {
	f();
	k();
}

int k() {
	pxx=&xx;
}

void x() {
	y(1);
}

void y(int x) {

}

int main() {
	int *p;
	p = &xx;
	k();
	return 0;
}
