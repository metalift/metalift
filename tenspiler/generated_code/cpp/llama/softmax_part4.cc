#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;

vector<float> softmax_part4(vector<float> unnormalized_output, int max_pos, float sum) {
    vector<float> output;
    for (int i = 0; i < max_pos; i++) {
        output.push_back(unnormalized_output[i] / sum);
    }
    return output;
}
