#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;

float softmax_part1(vector<float> input, int max_pos) {
    float max_val = input[0];
    for (int i = 1; i < max_pos; i++)
        if (input[i] > max_val)
            max_val = input[i];
    return max_val;
}
