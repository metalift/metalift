#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;


vector<vector<int32_t>> matrix_add_matrix(vector<vector<int32_t>> from_matrix, vector<vector<int32_t>> to_matrix)
{
    int i, j;
    vector<vector<int32_t>> out;
    for (i = 0; i < from_matrix.size(); ++i) {
        vector<int32_t> row_vec;
        for (j = 0; j < from_matrix[0].size(); ++j) {
            row_vec.push_back(from_matrix[i][j] + to_matrix[i][j]);
        }
        out.push_back(row_vec);
    }
    return out;
}
