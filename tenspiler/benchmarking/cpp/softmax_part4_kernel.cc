#include <iostream>
#include <vector>
#include <chrono>

#include "utils.h"

using namespace std;
using namespace std::chrono;

#include <cmath>

std::chrono::time_point<std::chrono::high_resolution_clock> start_time;
std::chrono::time_point<std::chrono::high_resolution_clock> end_time;

float softmax_part1(vector<float> input, int max_pos) {
    float max_val = input[0];
    for (int i = 1; i < max_pos; i++)
        if (input[i] > max_val)
            max_val = input[i];
    return max_val;
}


vector<float> softmax_part2(vector<float> input, int max_pos, float max_val) {
    vector<float> output;
    for (int i = 0; i < max_pos; i++) {
        float cur = exp(input[i] - max_val);
        output.push_back(cur);
    }
    return output;
}

float softmax_part3(vector<float> output, int max_pos) {
    float sum = 0;
    for (int i = 0; i < max_pos; i++) {
        sum += output[i];
    }
    return sum;
}

vector<float> softmax_part4_kernel(vector<float> unnormalized_output, int max_pos, float sum) {
    vector<float> output;
    start_time = high_resolution_clock::now();
    for (int i = 0; i < max_pos; i++) {
        output.push_back(unnormalized_output[i] / sum);
    }
    end_time = high_resolution_clock::now();
    return output;
}

int main() {
    setup_timer(false, true, false);

    vector<long long> times;
    size_t count = attn_weights.size();
    for (int i = 0; i < 10; i++) {
        long long time = 0;
        for (int j = 0; j < count; j++) {
            vector<float> inp1 = flatten(attn_weights[j]);
            int max_pos = inp1.size();

            float max_val = softmax_part1(inp1, max_pos);
            vector<float> output = softmax_part2(inp1, max_pos, max_val);
            float sum = softmax_part3(output, max_pos);

            softmax_part4_kernel(output, max_pos, sum);
            time += duration_cast<microseconds>(end_time - start_time).count();
        }
        times.push_back(time);
    }


    cout << "Execution Time: " << average(times) / 1000.0 << " ms +/-" << stdiv(times) / 1000.0 << endl;
    return 0;
}
