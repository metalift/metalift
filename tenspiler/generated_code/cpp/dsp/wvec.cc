#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;


vector<int32_t> wvec(vector<int32_t> a, vector<int32_t> b, int32_t m, int n) {
    vector<int32_t> out;
    for (int i = 0; i < n; ++i) {
        out.push_back(m * a[i] + b[i]);
    }
    return out;
}
