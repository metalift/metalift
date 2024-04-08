#include <vector>
using namespace std;

vector<vector<int>> scale_matrix(vector<vector<int>> m, int scale) {
    int i,j;
    vector<vector<int>> out;
    for (i = 0; i < m.size(); ++i) {
        vector<int> row_vec;
        for (j = 0; j < m[0].size(); ++j) {
            row_vec.push_back(m[i][j] * scale);
        }
        out.push_back(row_vec);
    }
    return out;
}

// matrix_scalar_mul(scale, m)
