#include <iostream>
#include <vector>
#include <chrono>

#include "utils.h"

using namespace std;
using namespace std::chrono;

#include <cmath>

std::chrono::time_point<std::chrono::high_resolution_clock> start_time;
std::chrono::time_point<std::chrono::high_resolution_clock> end_time;

vector<float> transformer_part3_kernel(vector<float> input, int hidden_dim) {
    vector<float> output;
    start_time = high_resolution_clock::now();
    for (int i = 0; i < hidden_dim; i++) {
        float curr = 1 / (1 + exp(-input[i])) * input[i];
        output.push_back(curr);
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
            int hidden_dim = inp1.size();

            transformer_part3_kernel(inp1, hidden_dim);
            time += duration_cast<microseconds>(end_time - start_time).count();
        }
        times.push_back(time);
    }


    cout << "Execution Time: " << average(times) / 1000.0 << " ms +/-" << stdiv(times) / 1000.0 << endl;
    return 0;
}
