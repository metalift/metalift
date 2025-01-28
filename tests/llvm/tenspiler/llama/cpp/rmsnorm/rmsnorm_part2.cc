#include <vector>
using namespace std;

int integer_sqrt(int x) { return x; }

vector<int> rmsnorm_part2(vector<int> input, vector<int> weight, int ss) {
    vector<int> output;
    int size = input.size();
    int inv_ss = 1 / integer_sqrt(ss / size + 1);
    for (int i = 0; i < input.size(); i++)
        output.push_back(inv_ss * input[i] * weight[i]);
    return output;
}
// def rmsnorm_part2_ps(input weight ss rmsnorm_part2_rv)
// rmsnorm_part2_rv == vec_scalar_mul((1 / integer_sqrt(((ss / list_length(input)) + 1))), vec_elemwise_mul(input, weight))
