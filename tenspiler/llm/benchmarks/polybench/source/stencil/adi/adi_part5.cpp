#include <vector>
using namespace std;

vector<vector<int>> adi_part5(
    int n,
    vector<vector<int>> X,
    vector<vector<int>> A,
    vector<vector<int>> B
) {
    vector<vector<int>> out;
    for (int i1 = 1; i1 < n; i1++) {
        vector<int> row_vec;
        for (int i2 = 0; i2 < n; i2++) {
            int curr = X[i1][i2] - X[i1-1][i2] * A[i1][i2] / B[i1-1][i2];
            row_vec.push_back(curr);
        }
        out.push_back(row_vec);
    }
    return out;
}
