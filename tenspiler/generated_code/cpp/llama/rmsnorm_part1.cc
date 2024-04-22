#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;

float rmsnorm_part1(vector<float> input, vector<float> weight) {
    float ss = 0;
    for (int i = 0; i < input.size(); i++)
        ss += input[i] * input[i];
    return ss;
}
