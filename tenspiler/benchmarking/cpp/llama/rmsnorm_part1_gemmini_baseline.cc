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

float rmsnorm_part1(vector<float> input, vector<float> weight) {
    start_time_k = high_resolution_clock::now();
    float ss = 0;
    for (int i = 0; i < input.size(); i++)
        ss += input[i] * input[i];
    end_time_k = high_resolution_clock::now();
    return ss;
}

int main() {

    vector<long long> times;
    vector<long long> times_k;
    size_t count = 241;
    for (int i = 0; i < 10; i++) {
        long long time = 0;
        long long time_k = 0;
        for (int j = 0; j < count; j++) {
            vector<float> inp1 = random_vector(676);
            vector<float> inp2 = random_vector(676);

            auto start_time = high_resolution_clock::now();
            auto result = rmsnorm_part1(inp2, inp1);
            auto end_time = high_resolution_clock::now();

            cout << result << endl;

            time += duration_cast<microseconds>(end_time - start_time).count();
            time_k += duration_cast<microseconds>(end_time_k - start_time_k).count();
        }
        times.push_back(time);
        times_k.push_back(time_k);

    }

    cout << "rmsnorm_part1_gemmini_baseline" << endl;
    cout << average(times) / 1000.0 << " " << stdiv(times) / 1000.0 << endl;
    cout << average(times_k) / 1000.0 << " " << stdiv(times_k) / 1000.0 << endl;
    return 0;
}
