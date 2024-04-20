#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;

vector<float> matmul(vector<vector<float>> weight, vector<float> input) {
    vector<float> output;
    int m = weight.size();
    int n = input.size();
    for (int row = 0; row < m; row++) {
        float curr = 0;
        for (int col = 0; col < n; col++) {
            curr += weight[row][col] * input[col];
        }
        output.push_back(curr);
    }
    return output;
}
