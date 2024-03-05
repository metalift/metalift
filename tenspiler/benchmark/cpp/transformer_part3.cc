#include <iostream>
#include <vector>
#include <chrono>

#include "utils.h"

using namespace std;
using namespace std::chrono;

#include <cmath>

vector<float> transformer_part3(vector<float> input, int hidden_dim) {
    vector<float> output;
    for (int i = 0; i < hidden_dim; i++) {
        float curr = 1 / (1 + exp(-input[i])) * input[i];
        output.push_back(curr);
    }
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

            auto start_time = high_resolution_clock::now();
            transformer_part3(inp1, hidden_dim);
            auto end_time = high_resolution_clock::now();
            time += duration_cast<microseconds>(end_time - start_time).count();
        }
        times.push_back(time);
    }


    cout << "Execution Time: " << average(times) / 1000.0 << " ms +/-" << stdiv(times) / 1000.0 << endl;
    return 0;
}
