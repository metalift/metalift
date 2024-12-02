#include <vector>
using namespace std;

vector<vector<int>> matrix_add_matrix(vector<vector<int>> from_matrix, vector<vector<int>> to_matrix)
{
    int i, j;
    vector<vector<int>> out;
    for (i = 0; i < from_matrix.size(); ++i) {
        vector<int> row_vec;
        for (j = 0; j < from_matrix[0].size(); ++j) {
            row_vec.push_back(from_matrix[i][j] + to_matrix[i][j]);
        }
        out.push_back(row_vec);
    }
    return out;
}

// matrix_elemwise_add(from_matrix, to_matrix)
