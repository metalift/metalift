#include <vector>
using namespace std;

vector<vector<int>> fdtd_2d_part3(
    int nx,
    int ny,
    vector<vector<int>> ex,
    vector<vector<int>> ey,
    vector<vector<int>> hz
) {
    vector<vector<int>> out;
    for (int i = 0; i < nx - 1; i++) {
        vector<int> row_vec;
        for (int j = 0; j < ny - 1; j++) {
            int curr = hz[i][j] - 7 * (ex[i][j+1] - ex[i][j] + ey[i+1][j] - ey[i][j]);
            row_vec.push_back(curr);
        }
        out.push_back(row_vec);
    }
    return out;
}
