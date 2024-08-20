#include <vector>
using namespace std;

vector<vector<int>> seidel_2d(
    int n,
    vector<vector<int>> A
) {
    vector<vector<int>> out;
    for (int i = 1; i <= n - 2; i++) {
        vector<int> row_vec;
        for (int j = 1; j <= n - 2; j++) {
            int curr = (A[i-1][j-1] + A[i-1][j] + A[i-1][j+1] + A[i][j-1] + A[i][j] + A[i][j+1] + A[i+1][j-1] + A[i+1][j] + A[i+1][j+1]) / 9;
            row_vec.push_back(curr);
        }
        out.push_back(row_vec);
    }
    return out;
}
