#include <stdio.h>

int ga, gb, gc;
int *pga, *pgb, *pgc;
int **ppga, **ppgb, **ppgc;
int garr[100];

int g(){
	pgc = &gc;
}

int f(int x) {
	pga = &ga;
	pgb = &gb;
	garr[3] = 10;
	int larr[10];
	larr[0] = 10;
	g();
	return 0;
}

int main() {
	if(*pga > garr[1]){
		f(3);
		int i;
		//garr[i] = 10;
	}


	return 0;
}

