#include <vector>
using namespace std;

int integer_exp(int x) { return x; }

vector<int> transformer_part3(vector<int> input, int hidden_dim) {
    vector<int> output;
    for (int i = 0; i < hidden_dim; i++) {
        int curr = input[i] * (1 / (1 + integer_exp(0 - input[i])));
        output.push_back(curr);
    }
    return output;
}
