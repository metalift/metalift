#include <vector>
using namespace std;

vector<vector<int>> jacobi_2d(
    int n,
    vector<vector<int>> A
) {
    vector<vector<int>> out;
    for (int i = 1; i < n - 1; i++) {
        vector<int> row_vec;
        for (int j = 1; j < n - 1; j++) {
            int curr = 2 * (A[i][j] + A[i][j - 1] + A[i][j + 1] + A[i + 1][j] + A[i - 1][j]);
            row_vec.push_back(curr);
        }
        out.push_back(row_vec);
    }
    return out;
}
