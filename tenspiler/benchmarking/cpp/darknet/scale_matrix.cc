#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;


vector<vector<int32_t>> scale_matrix(vector<vector<int32_t>> m, int32_t scale) {
    int i,j;
    vector<vector<int32_t>> out;
    for (i = 0; i < m.size(); ++i) {
        vector<int32_t> row_vec;
        for (j = 0; j < m[0].size(); ++j) {
            row_vec.push_back(m[i][j] * scale);
        }
        out.push_back(row_vec);
    }
    return out;
}
