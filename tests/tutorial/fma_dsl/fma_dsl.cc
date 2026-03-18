int test(int base, int arg1, int base2, int arg2)
{
    int a = 0;

    a = (base + base2) + arg1 * arg2;

    a = a + a;

    return a;
}
