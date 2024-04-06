#include <vector>
using namespace std;

vector<int> cube_in_place(vector<int> arr, int n) {
    vector<int> out;
    for (int i = 0; i < n; ++i) {
        out.push_back(arr[i] * arr[i] * arr[i]);
    }
    return out;
}

// vec_elemwise_mul(vec_slice(arr, 0, n), vec_elemwise_mul(vec_slice(arr, 0, n), vec_slice(arr, 0, n)))
