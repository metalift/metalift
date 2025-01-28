#include <iostream>
#include <vector>
#include <chrono>
#include <stdio.h>
#include <stdlib.h>

#include "utils.h"

using namespace std;
using namespace std::chrono;

#include <cmath>

std::chrono::time_point<std::chrono::high_resolution_clock> start_time_k;
std::chrono::time_point<std::chrono::high_resolution_clock> end_time_k;

float rmsnorm_part1(vector<float> input, vector<float> weight) {
    float ss = 0;
    for (int i = 0; i < input.size(); i++)
        ss += input[i] * input[i];
    return ss;
}

vector<float> rmsnorm_part2(vector<float> input, vector<float> weight, float ss) {
    start_time_k = high_resolution_clock::now();
    vector<float> output;
    int size = input.size();
    float inv_ss = 1 / sqrt(ss / size + 1);
    for (int i = 0; i < input.size(); i++)
        output.push_back(inv_ss * input[i] * weight[i]);
    end_time_k = high_resolution_clock::now();
    return output;
}

int main() {
    setup_timer(true, false, false);

    vector<long long> times;
    vector<long long> times_k;
    size_t count = weights.size();
    for (int i = 0; i < 10; i++) {
        long long time = 0;
        long long time_k = 0;
        for (int j = 0; j < count; j++) {

            vector<float> inp1 = flatten(weights[j]);

            vector<float> inp2 = flatten(w_input[j]);
            float ss = rmsnorm_part1(inp2, inp1);

            auto start_time = high_resolution_clock::now();
            rmsnorm_part2(inp2, inp1, ss);
            auto end_time = high_resolution_clock::now();

            time += duration_cast<microseconds>(end_time - start_time).count();
            time_k += duration_cast<microseconds>(end_time_k - start_time_k).count();
        }
        times.push_back(time);
        times_k.push_back(time_k);
    }

    cout << "rmsnorm_part2" << endl;
    cout << average(times) / 1000.0 << " " << stdiv(times) / 1000.0 << endl;
    cout << average(times_k) / 1000.0 << " " << stdiv(times_k) / 1000.0 << endl;
    return 0;
}
