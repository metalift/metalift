#include <vector>
using namespace std;

vector<vector<int>> fdtd_2d_part1(
    int nx,
    int ny,
    vector<vector<int>> ey,
    vector<vector<int>> hz
) {
    vector<vector<int>> out;
    for (int i = 1; i < nx; i++) {
        vector<int> row_vec;
        for (int j = 0; j < ny; j++) {
            int curr = ey[i][j] - 5 * (hz[i][j] - hz[i - 1][j]);
            row_vec.push_back(curr);
        }
        out.push_back(row_vec);
    }
    return out;
}
