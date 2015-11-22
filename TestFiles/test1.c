#include <stdio.h>

int xx;
int *pxx;
int yy;

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
	int loc;
	pxx = &loc;
}

void j() {
	j();
	*pxx = 10;
}

void h() {
	f();
	k();
	*pxx=6;
}

void k() {
	pxx = &yy;
}

void x() {
	y();
}

void y() {
}

int main(){
	int *p;
	p = &xx;
	k();
	return 0;
}
