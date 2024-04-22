#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;


vector<int32_t> mat1x3(int N, vector<vector<int32_t>> h, vector<int32_t> x) {
    vector<int32_t> y;
    for (int i = 0; i < N; i++) {
        int32_t sum = 0;
        for (int f = 0; f < N; f++) {
            sum += h[i][f] * x[f];
        }
        y.push_back(sum);
    }
    return y;
}
