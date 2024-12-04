#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;

float softmax_part3(vector<float> output, int max_pos) {
    float sum = 0;
    for (int i = 0; i < max_pos; i++) {
        sum += output[i];
    }
    return sum;
}
