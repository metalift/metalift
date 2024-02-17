#include <vector>
using namespace std;

int integer_exp(int x) { return x; }

vector<int> softmax_part2(vector<int> input, int max_pos, int max_val) {
    vector<int> output;
    for (int i = 0; i < max_pos; i++) {
        int cur = integer_exp(input[i] - max_val);
        output.push_back(cur);
    }
    return output;
}

// def softmax_part2_ps(input max_pos max_val softmax_part2_rv)
// softmax_part2_rv == vec_map(vec_scalar_sub(max_val, list_take(input, max_pos)), map_int_to_int)

// def map_int_to_int(int_x)
// integer_exp(int_x)
