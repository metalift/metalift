#include <vector>
using namespace std;

vector<int> voffset(vector<int> arr, int v, int n) {
    vector<int> out;
    for (int i = 0; i < n; ++i) {
        out.push_back(arr[i] + v);
    }
    return out;
}

// vec_scalar_add(v, vec_slice(arr, 0, n))
