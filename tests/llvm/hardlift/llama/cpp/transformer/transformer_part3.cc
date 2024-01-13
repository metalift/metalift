#include <vector>
using namespace std;

int integer_exp(int x) { return x; }

vector<int> transformer_part3(vector<int> input, int hidden_dim) {
    vector<int> output;
    for (int i = 0; i < hidden_dim; i++) {
        int curr = input[i] * (1 / (1 + integer_exp(-input[i])));
        output.push_back(curr);
    }
    return output;
}
// def transformer_part3_ps(input hidden_dim transformer_part3_rv)
// list_eq(transformer_part3_rv, vec_elemwise_mul(list_take(input, hidden_dim), scalar_vec_div(1, vec_scalar_add(1, vec_map(scalar_vec_sub(0, list_take(input, hidden_dim)), map_int_to_int)))))

// def map_int_to_int(int_x)
// integer_exp(int_x)