#include <vector>
using namespace std;

int sum_elts(vector<int> arr, int n) {
    int sum = 0;
    for (int i = 0; i < n; ++i) {
        sum += arr[i];
    }
    return sum;
}

// reduce_sum(vec_slice(arr, 0, n))
