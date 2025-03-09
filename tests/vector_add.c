// Can utilize Intel AVX Intrinsics SIMD instructions (add_pd and reduce_add_pd)
int test(int a1, int a2, int a3, int a4, int b1, int b2, int b3, int b4) {
    int res = a1 + a2 + a3 + a4;
    res += b1 + b2 + b3 + b4;
    res += a1 + a2 + a3 + a4;
    res += b1 + b2 + b3 + b4;
    res += a1 + a2 + a3 + a4;
    return res;
}
