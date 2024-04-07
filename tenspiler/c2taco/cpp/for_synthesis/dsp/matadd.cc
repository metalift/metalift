#include <vector>
using namespace std;

vector<vector<int>> matadd(vector<vector<int>> matA, vector<vector<int>> matB, int m, int n) {
    vector<vector<int>> out;
    for (int i = 0; i < m; ++i) {
        vector<int> row_vec;
        for (int j = 0; j < n; ++j) {
            row_vec.push_back(matA[i][j] + matB[i][j]);
        }
        out.push_back(row_vec);
    }
    return out;
}

// matrix_elemwise_add(matrix_col_slice(matrix_row_slice(matA, 0, m), 0, n), matrix_col_slice(matrix_row_slice(matB, 0, m), 0, n))
