#include <vector>
using namespace std;

int test_sqrt(int x) { return x; }

vector<int> silu(vector<int> input, int hidden_dim) {
    vector<int> output;
    for (int i = 0; i < hidden_dim; i++) {
        int curr = 1 / (1 + test_sqrt(input[i])) * input[i];
        output.push_back(curr);
    }
    return output;
}
// def silu_ps(input hidden_dim silu_rv)
// silu_rv == vec_elemwise_mul(scalar_vec_div(1, vec_scalar_add(1, vec_map(list_take(input, hidden_dim), map_int_to_int))), list_take(input, hidden_dim))

// def map_int_to_int(int_x)
// test_sqrt(int_x)