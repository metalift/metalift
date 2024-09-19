#include <vector>
using namespace std;

vector<int> adi_part3(
    int n,
    vector<vector<int>> X,
    vector<vector<int>> B
) {
    vector<int> out;
    for (int i1 = 0; i1 < n; i1++) {
        out.push_back(X[i1][n-1] / B[i1][n-1]);
    }
    return out;
}
