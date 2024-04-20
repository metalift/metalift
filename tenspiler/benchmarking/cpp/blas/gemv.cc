#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;

vector<int32_t> gemv(int M, int N, vector<vector<int32_t>> A, vector<int32_t> x) {
    vector<int32_t> y;
    for (int i = 0; i < M; ++i) {
        int sum = 0;
        for (int j = 0; j < N; ++j) {
            sum += A[i][j] * x[j];
        }
        y.push_back(sum);
    }
    return y;
}
