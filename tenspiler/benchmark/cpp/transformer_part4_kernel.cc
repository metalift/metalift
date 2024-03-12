#include <iostream>
#include <vector>
#include <chrono>

#include "utils.h"

using namespace std;
using namespace std::chrono;

std::chrono::time_point<std::chrono::high_resolution_clock> start_time;
std::chrono::time_point<std::chrono::high_resolution_clock> end_time;

vector<float> transformer_part4_kernel(vector<float> input1, vector<float> input2, int hidden_dim) {
    vector<float> output;
    start_time = high_resolution_clock::now();
    for (int i = 0; i < hidden_dim; i++) {
        output.push_back(input1[i] * input2[i]);
    }
    end_time = high_resolution_clock::now();
    return output;
}

int main() {
    setup_timer(true, false, false);

    vector<long long> times;
    size_t count = weights.size();
    for (int i = 0; i < 10; i++) {
        long long time = 0;
        for (int j = 0; j < count; j++) {
            vector<float> inp1 = flatten(weights[j]);
            vector<float> inp2 = flatten(w_input[j]);
            int hidden_dim = inp2.size();

            transformer_part4_kernel(inp1, inp2, hidden_dim);
            time += duration_cast<microseconds>(end_time - start_time).count();
        }
        times.push_back(time);
    }


    cout << "Execution Time: " << average(times) / 1000.0 << " ms +/-" << stdiv(times) / 1000.0 << endl;
    return 0;
}
