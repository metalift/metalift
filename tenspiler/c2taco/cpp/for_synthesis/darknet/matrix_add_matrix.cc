#include <vector>
using namespace std;

vector<vector<int>> matrix_add_matrix(vector<vector<int>> from, vector<vector<int>> to)
{
    int i, j;
    vector<vector<int>> out;
    for(i = 0; i < from.size(); ++i){
        vector<int> row_vec;
        for(j = 0; j < from[0].size(); ++j){
            row_vec.push_back(from[i][j] + to[i][j]);
        }
        out.push_back(row_vec);
    }
    return out;
}

// matrix_elemwise_add(from, to)
