#include <stdio.h>

int xx;

void f();
void g();
void h();
void i();
void k();
void j();
void x();
void y();

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

void k() {
}

void x() {
	y();
}

void y() {
}

int main(){
	int *p;
	p = &xx;
	return 0;
}
