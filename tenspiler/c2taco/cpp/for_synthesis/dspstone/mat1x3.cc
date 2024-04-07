#include <vector>
using namespace std;

vector<int> mat1x3(int N, vector<vector<int>> h, vector<int> x) {
    vector<int> y;
    for (int i = 0; i < N; i++) {
        int sum = 0;
        for (int f = 0; f < N; f++) {
            sum += h[i][f] * x[f];
        }
        y.push_back(sum);
    }
    return y;
}

// matmul(matrix_col_slice(matrix_row_slice(h, 0, N), 0, N), vec_slice(x, 0, N))
