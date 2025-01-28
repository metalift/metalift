#include <iostream>
#include <vector>
#include <chrono>
#include <stdio.h>
#include <stdlib.h>

#include "utils.h"

using namespace std;
using namespace std::chrono;

#include <cmath>

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

std::chrono::time_point<std::chrono::high_resolution_clock> start_time_k;
std::chrono::time_point<std::chrono::high_resolution_clock> end_time_k;

float softmax_part3(vector<float> output, int max_pos) {
    start_time_k = high_resolution_clock::now();
    float sum = 0;
    for (int i = 0; i < max_pos; i++) {
        sum += output[i];
    }
    end_time_k = high_resolution_clock::now();
    return sum;
}

int main() {
    setup_timer_7b(false, true, false);

    vector<long long> times;
    vector<long long> times_k;
    size_t count = attn_weights.size();
    for (int i = 0; i < 10; i++) {
        long long time = 0;
        long long time_k = 0;
        for (int j = 0; j < count; j++) {
            vector<float> inp1 = flatten(attn_weights[j]);
            int max_pos = inp1.size();

            float max_val = softmax_part1(inp1, max_pos);
            vector<float> output = softmax_part2(inp1, max_pos, max_val);

            auto start_time = high_resolution_clock::now();
            auto result = softmax_part3(output, max_pos);
            auto end_time = high_resolution_clock::now();

            cout << result << endl;

            time += duration_cast<microseconds>(end_time - start_time).count();
            time_k += duration_cast<microseconds>(end_time_k - start_time_k).count();

        }
        times.push_back(time);
        times_k.push_back(time_k);
    }
    cout << "softmax_part3_mlx_baseline" << endl;
    cout << average(times) / 1000.0 << " " << stdiv(times) / 1000.0 << endl;
    cout << average(times_k) / 1000.0 << " " << stdiv(times_k) / 1000.0 << endl;
    return 0;
}
