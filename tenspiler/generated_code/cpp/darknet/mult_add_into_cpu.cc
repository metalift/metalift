#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;

vector<int32_t> mult_add_into_cpu(int N, vector<int32_t> X, vector<int32_t> Y, vector<int32_t> Z) {
    int i;
    vector<int32_t> out;
    for(i = 0; i < N; ++i) {
        out.push_back(Z[i] + X[i] * Y[i]);
    }
    return out;
}
