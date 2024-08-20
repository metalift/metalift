
#include <vector>
using namespace std;

vector<vector<int>> adi_part4(
    int n,
    vector<vector<int>> X,
    vector<vector<int>> A,
    vector<vector<int>> B
) {
    vector<vector<int>> out;
    for (i1 = 0; i1 < n; i1++) {
        vector<int> row_vec;
        for (i2 = 0; i2 < n-2; i2++) {
            int curr = (X[i1][n-2-i2] - X[i1][n-2-i2-1] * A[i1][n-i2-3]) / B[i1][n-3-i2];
            row_vec.push_back(curr);
        }
        out.push_back(row_vec);
    }
    return out;
}
