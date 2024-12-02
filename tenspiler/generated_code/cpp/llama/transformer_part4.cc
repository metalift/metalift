#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;

vector<float> transformer_part4(vector<float> input1, vector<float> input2, int hidden_dim) {
    vector<float> output;
    for (int i = 0; i < hidden_dim; i++) {
        output.push_back(input1[i] * input2[i]);
    }
    return output;
}
