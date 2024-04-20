#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;


vector<int32_t> n_real_updates(int N, vector<int32_t> A, vector<int32_t> B, vector<int32_t> C) {
    vector<int32_t> D;
    for (int i = 0; i < N; i++) {
        int32_t curr = C[i] + A[i] * B[i];
        D.push_back(curr);
    }
    return D;
}
