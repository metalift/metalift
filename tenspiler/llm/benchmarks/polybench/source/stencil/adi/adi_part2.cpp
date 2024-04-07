#include <vector>
using namespace std;

vector<vector<int>> adi_part2(
    int n,
    vector<vector<int>> X,
    vector<vector<int>> A,
    vector<vector<int>> B
) {
    vector<vector<int>> out;
    for (int i1 = 0; i1 < n; i1++) {
        vector<int> row_vec;
        for (int i2 = 1; i2 < n; i2++) {
            int curr = B[i1][i2] - A[i1][i2] * A[i1][i2] / B[i1][i2-1];
            row_vec.push_back(curr);
        }
        out.push_back(row_vec);
    }
    return out;
}
