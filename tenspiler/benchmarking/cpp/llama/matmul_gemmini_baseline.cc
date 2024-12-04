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

vector<float> matmul(vector<vector<float>> weight, vector<float> input) {
    start_time_k = high_resolution_clock::now();
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
    end_time_k = high_resolution_clock::now();
    return output;
}

int main() {

    vector<long long> times;
    vector<long long> times_k;
    size_t count = 240;
    for (int i = 0; i < 10; i++) {
        long long time = 0;
        long long time_k = 0;
        for (int j = 0; j < count; j++) {
            vector<vector<float>> weight = random_matrix(832, 832);
            vector<float> inp1 = random_vector(832);

            auto start_time = high_resolution_clock::now();
            matmul(weight, inp1);
            auto end_time = high_resolution_clock::now();

            time += duration_cast<microseconds>(end_time - start_time).count();
            time_k += duration_cast<microseconds>(end_time_k - start_time_k).count();
        }
        times.push_back(time);
        times_k.push_back(time_k);
    }
    cout << "matmul_gemmini_baseline" << endl;
    cout << average(times) / 1000.0 << " " << stdiv(times) / 1000.0 << endl;
    cout << average(times_k) / 1000.0 << " " << stdiv(times_k) / 1000.0 << endl;
    return 0;
}
