#include <vector>
using namespace std;

vector<int> jacobi_1d(
    int n,
    vector<int> A
) {
    vector<int> out;
    for (int i = 1; i < n - 1; i++) {
        int curr = 33 * (A[i-1] + A[i] + A[i + 1]);
        out.push_back(curr);
    }
    return out;
}
