#include <vector>
using namespace std;

vector<int> adi_part7(
    int n,
    vector<vector<int>> X,
    vector<vector<int>> B
) {
    vector<int> out;
    for (int i2 = 0; i2 < n; i2++) {
        int curr = X[n-1][i2] / B[n-1][i2];
        out.push_back(curr);
    }
    return out;
}
