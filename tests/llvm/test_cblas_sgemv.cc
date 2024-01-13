#include <vector>
using namespace std;

vector<int> test_cblas_sgemv(
    int alpha,
    vector<vector<int>> a,
    vector<int>x,
    int beta,
    vector<int> y
) {
    vector<int> z;

    // value of m
    if (a.size() != y.size()) return z;
    // value of n
    if (a[0].size() != x.size()) return z;

    int m = a.size();
    int n = x.size();

    // a is of size m * n, x is of size n x 1, y is of size m x 1
    for (int i = 0; i < m; i++) {
        int res = 0;
        for (int j = 0; j < n; j++) {
            // summation(a[i][j] * x[j]) over i=1 to m, j=1 to n
            res += a[i][j] * x[j];
        }
        z.push_back(alpha * res + beta * y[i]);
    }

    return z;
}
