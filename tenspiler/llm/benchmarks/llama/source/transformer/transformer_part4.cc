#include <vector>
using namespace std;

vector<int> transformer_part4(vector<int> input1, vector<int> input2, int hidden_dim) {
    vector<int> output;
    for (int i = 0; i < hidden_dim; i++) {
        output.push_back(input1[i] * input2[i]);
    }
    return output;
}
