#include <vector>
using namespace std;

vector<vector<vector<int>>> elemwise_add(
    vector<vector<vector<int>>> tensor3d_x,
    vector<vector<vector<int>>> tensor3d_y
) {
    vector<vector<vector<int>>> out;
    int m = tensor3d_x.size();
    int n = tensor3d_x[0].size();
    int o = tensor3d_x[0][0].size();

    for (int i = 0; i < m; i++) {
        vector<vector<int>> matrix;
        for (int j = 0; j < n; j++) {
            vector<int> lst;
            for (int k = 0; k < o; k++) {
                lst.push_back(tensor3d_x[i][j][k] + tensor3d_y[i][j][k]);
            }
            matrix.push_back(lst);
        }
        out.push_back(matrix);
    }

    return out;
}
