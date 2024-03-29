#include <vector>
using namespace std;

vector<vector<int>> fdtd_2d_part1(
    int nx,
    int ny,
    vector<vector<int>> ey,
    vector<vector<int>> hz
) {
    vector<vector<int>> out;
    for (int i = 0; i < nx; i++) {
        vector<int> row_vec;
        for (int j = 1; j < ny; j++) {
            int curr = 2 * (hz[i][j] - hz[i][j - 1]);
            row_vec.push_back(curr);
        }
        out.push_back(row_vec);
    }
    return out;
}
