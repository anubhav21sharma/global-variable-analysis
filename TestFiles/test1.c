#include <stdio.h>

int ga, gb, gc;
int *pga, *pgb, *pgc;

int fn1(int i) {
	return 0;
}

int fn2(int i) {
	return fn1(0);
}

int main() {
	switch(gb){
	case 1:
		return gc;
	case 2:
		break;
	}
	return ga;
}

