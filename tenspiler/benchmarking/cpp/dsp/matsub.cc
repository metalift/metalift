#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;


vector<vector<int32_t>> matsub(
    vector<vector<int32_t>> matA,
    vector<vector<int32_t>> matB,
    int m,
    int n
) {
    vector<vector<int32_t>> out;
    for (int i = 0; i < m; ++i) {
        vector<int32_t> row_vec;
        for (int j = 0; j < n; ++j) {
            row_vec.push_back(matA[i][j] - matB[i][j]);
        }
        out.push_back(row_vec);
    }
    return out;
}