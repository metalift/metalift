#include <vector>
using namespace std;

int lmsfir1(int NTAPS, vector<int> input, vector<int> coefficient) {
    int sum = 0;
    for (int i = 0; i < NTAPS; ++i) {
        sum += input[i] * coefficient[i];
    }
    return sum;
}

// reduce_sum(vec_elemwise_mul(vec_slice(input, 0, NTAPS), vec_slice(coefficient, 0, NTAPS)))
