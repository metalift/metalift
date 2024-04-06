#include <vector>
using namespace std;

vector<int> array_inc(vector<int> arr, int n) {
    vector<int> out;
    for (int i = 0; i < n; ++i) {
        out.push_back(arr[i] + 1);
    }
    return out;
}

// vec_scalar_add(1, vec_slice(arr, 0, n))
