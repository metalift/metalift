#include <vector>
using namespace std;

int len_sq(vector<int> arr, int n) {
    int l = 0;
    for (int i = 0; i < n; ++i) {
        l += arr[i] * arr[i];
    }
    return l;
}

// reduce_sum(vec_elemwise_mul(vec_slice(arr, 0, n), vec_slice(arr, 0, n)))
