#include <iostream>
#include <vector>
#include <chrono>
#include <stdio.h>
#include <stdlib.h>

#include "utils.h"

using namespace std;
using namespace std::chrono;

std::chrono::time_point<std::chrono::high_resolution_clock> start_time_k;
std::chrono::time_point<std::chrono::high_resolution_clock> end_time_k;

vector<float> transformer_part4(vector<float> input1, vector<float> input2, int hidden_dim) {
    start_time_k = high_resolution_clock::now();
    vector<float> output;
    for (int i = 0; i < hidden_dim; i++) {
        output.push_back(input1[i] * input2[i]);
    }
    end_time_k = high_resolution_clock::now();
    return output;
}

int main() {
    setup_timer_7b(true, false, false);

    vector<long long> times;
    vector<long long> times_k;
    size_t count = weights.size();
    for (int i = 0; i < 10; i++) {
        long long time = 0;
        long long time_k = 0;
        for (int j = 0; j < count; j++) {

            vector<float> inp1 = flatten(weights[j]);

            vector<float> inp2 = flatten(w_input[j]);
            int hidden_dim = inp2.size();

            auto start_time = high_resolution_clock::now();
            auto result = transformer_part4(inp1, inp2, hidden_dim);
            auto end_time = high_resolution_clock::now();

            time += duration_cast<microseconds>(end_time - start_time).count();
            time_k += duration_cast<microseconds>(end_time_k - start_time_k).count();

        }
        times.push_back(time);
        times_k.push_back(time_k);
    }
    cout << "transformer_part4_mlx_baseline" << endl;
    cout << average(times) / 1000.0 << " " << stdiv(times) / 1000.0 << endl;
    cout << average(times_k) / 1000.0 << " " << stdiv(times_k) / 1000.0 << endl;
    return 0;
}
