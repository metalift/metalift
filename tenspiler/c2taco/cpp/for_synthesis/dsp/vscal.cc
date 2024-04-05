#include <vector>
using namespace std;

vector<int> vscal(vector<int> arr, int v, int n) {
    vector<int> out;
    for (int i = 0; i < n; ++i) {
        out.push_back(v * arr[i]);
    }
    return out;
}

// vec_scalar_mul(v, vec_slice(arr, 0, n))
