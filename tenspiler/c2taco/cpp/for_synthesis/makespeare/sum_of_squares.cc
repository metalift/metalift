#include <vector>
using namespace std;

int sum_of_squares(vector<int> arr, int n) {
    int sum = 0;
    for (int i = 0; i < n; ++i) {
        sum += arr[i] * arr[i];
    }
    return sum;
}

// reduce_sum(vec_elemwise_mul(vec_slice(arr, 0, n), vec_slice(arr, 0, n)))
