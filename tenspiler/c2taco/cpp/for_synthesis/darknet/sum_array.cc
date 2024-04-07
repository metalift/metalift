#include <vector>
using namespace std;

int sum_array(vector<int> a, int n) {
    int i;
    int sum = 0;
    for (i = 0; i < n; ++i) {
        sum += a[i];
    }
    return sum;
}

// reduce_sum(vec_slice(a, 0, n))
