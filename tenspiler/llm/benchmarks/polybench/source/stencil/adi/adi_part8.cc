#include <vector>
using namespace std;

vector<vector<int>> adi_part8(
    int n,
    vector<vector<int>> X,
    vector<vector<int>> A,
    vector<vector<int>> B
) {
    vector<vector<int>> out;

    for (int i1 = 0; i1 < n-2; i1++) {
        vector<int> row_vec;
        for (int i2 = 0; i2 < n; i2++) {
            int curr = (X[n-2-i1][i2] - X[n-i1-3][i2] * A[n-3-i1][i2]) / B[n-2-i1][i2];
            row_vec.push_back(curr);
        }
        out.push_back(row_vec);
    }
    return out;
}
