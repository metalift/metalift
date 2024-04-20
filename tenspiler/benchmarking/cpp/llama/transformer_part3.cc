#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;

vector<float> transformer_part3(vector<float> input, int hidden_dim) {
    vector<float> output;
    for (int i = 0; i < hidden_dim; i++) {
        float curr = 1 / (1 + exp(-input[i])) * input[i];
        output.push_back(curr);
    }
    return output;
}
