#include <vector>
using namespace std;

int mag_array(vector<int> a, int n) {
    int i;
    int sum = 0;
    for(i = 0; i < n; ++i){
        sum += a[i] * a[i];
    }
    return sum;
}


// reduce_sum(vec_slice(a, 0, n), vec_slice(a, 0, n))
