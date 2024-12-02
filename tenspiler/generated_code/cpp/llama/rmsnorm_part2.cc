#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;

vector<float> rmsnorm_part2(vector<float> input, vector<float> weight, float ss) {
    vector<float> output;
    int size = input.size();
    float inv_ss = 1 / sqrt(ss / size + 1);
    for (int i = 0; i < input.size(); i++)
        output.push_back(inv_ss * input[i] * weight[i]);
    return output;
}
