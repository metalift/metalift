#include <vector>
using namespace std;

int rmsnorm_part1(vector<int> input, vector<int> weight) {
    int ss = 0;
    for (int i = 0; i < input.size(); i++)
        ss += input[i] * input[i];
    return ss;
}
inv0: input[0:i], input[-1:i], input[1:i]
0,-1,1,i,upper_bound-1,
input[int_var:int_var] for ps and inv
matrix[int_var:int_var].col_slice(int_var, int_var)
depth applies to index int_var, and operations on vectors

relaxed version: int_var can be +-1 from what we scan
// def rmsnorm_part1_ps(input weight rmsnorm_part1_rv)
// rmsnorm_part1_rv == reduce_sum(vec_elemwise_mul(input, input))
