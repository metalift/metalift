#include <vector>
using namespace std;

vector<int> transformer_part4(vector<int> input1, vector<int> input2, int hidden_dim) {
    vector<int> output;
    for (int i = 0; i < hidden_dim; i++) {
        output.push_back(input1[i] * input2[i]);
    }
    return output;
}
// def transformer_part4_ps(input1 input2 hidden_dim transformer_part4_rv)
// transformer_part4_rv == vec_elemwise_mul(list_take(input2, hidden_dim), list_take(input1, hidden_dim))
