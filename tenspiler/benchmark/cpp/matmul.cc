#include <iostream>
#include <vector>
#include <chrono>

#include "utils.h"

using namespace std;
using namespace std::chrono;

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

int main() {
    setup_timer(false, true, false);

    vector<long long> times;
    size_t count = attn_weights.size();
    for (int i = 0; i < 10; i++) {
        long long time = 0;
        for (int j = 0; j < count; j++) {
            vector<vector<float>> weight = attn_weights[j];
            vector<float> inp1 = aw_input[j];

            auto start_time = high_resolution_clock::now();
            matmul(weight, inp1);
            auto end_time = high_resolution_clock::now();

            time += duration_cast<microseconds>(end_time - start_time).count();
        }
        times.push_back(time);
    }


    cout << "Execution Time: " << average(times) / 1000.0 << " ms +/-" << stdiv(times) / 1000.0 << endl;
    return 0;
}
