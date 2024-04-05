#include <vector>
using namespace std;

vector<int> gemv(int M, int N, vector<vector<int>> A, vector<int> x) {
    vector<int> y;
    for (int i = 0; i < M; ++i) {
        int sum = 0;
        for (int j = 0; j < N; ++j) {
            sum += A[i][j] * x[j];
        }
        y.push_back(sum);
    }
    return y;
}

// matmul(matrix_col_slice(matrix_row_slice(A, 0, M), 0, N), vec_slice(x, 0, N))
