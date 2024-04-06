#include <vector>
using namespace std;

vector<int> fourth_in_place(vector<int> arr, int n) {
    vector<int> out;
    for (int i = 0; i < n; ++i) {
        int sq = arr[i] * arr[i];
        int fourth = sq * sq;
        out.push_back(fourth);
    }
    return out;
}

// vec_elemwise_mul(vec_elemwise_mul(vec_slice(arr, 0, n), vec_slice(arr, 0, n)), vec_elemwise_mul(vec_slice(arr, 0, n), vec_slice(arr, 0, n)))
