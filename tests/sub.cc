// Prevent function name mangling
extern "C" {
	int test(int a, int b)
	{
		return a + b;
	}
}
