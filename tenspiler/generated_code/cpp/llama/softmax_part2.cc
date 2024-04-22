#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;

vector<float> softmax_part2(vector<float> input, int max_pos, float max_val) {
    vector<float> output;
    for (int i = 0; i < max_pos; i++) {
        float cur = exp(input[i] - max_val);
        output.push_back(cur);
    }
    return output;
}
