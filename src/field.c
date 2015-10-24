int condition;

int main ()
{
	int * x, * y, *z;
	int a, b, c;

	if (condition)
		x = &a;
	else
		z = &a;
		x = &c;

	y = &b;
}
