#include <vector>
using namespace std;

vector<vector<int>> matmul_sca(vector<vector<int>> matA, int val, int m, int n) {
    vector<vector<int>> out;
    for (int i = 0; i < m; ++i) {
        vector<int> row_vec;
        for (int j = 0; j < n; ++j) {
            row_vec.push_back(matA[i][j] * val);
        }
        out.push_back(row_vec);
    }
    return out;
}

// matrix_scalar_mul(val, matrix_col_slice(matrix_row_slice(0, m), 0, n))
