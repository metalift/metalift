#include <vector>
using namespace std;

int rmsnorm_part1(vector<int> input, vector<int> weight) {
    int ss = 0;
    for (int i = 0; i < input.size(); i++)
        ss += input[i] * input[i];
    return ss;
}

// def rmsnorm_part1_ps(input weight rmsnorm_part1_rv)
// rmsnorm_part1_rv == reduce_sum(vec_elemwise_mul(input, input))
