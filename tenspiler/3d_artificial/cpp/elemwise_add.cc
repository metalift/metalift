#include <vector>
using namespace std;

vector<vector<vector<int>>> elemwise_add(
    vector<vector<vector<int>>> a,
    vector<vector<vector<int>>> b
) {
    vector<vector<vector<int>>> out;
    int m = a.size();
    int n = a[0].size();
    int o = a[0][0].size();

    for (int i = 0; i < m; i++) {
        vector<vector<int>> matrix;
        for (int j = 0; j < n; j++) {
            vector<int> lst;
            for (int k = 0; k < o; k++) {
                lst.push_back(a[i][j][k] + b[i][j][k]);
            }
            matrix.push_back(lst);
        }
        out.push_back(matrix);
    }

    return out;
}
