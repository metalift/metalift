#include <iostream>
#include <vector>
#include <chrono>
#include <tuple>

#include "utils.h"

using namespace std;
using namespace std::chrono;

std::chrono::time_point<std::chrono::high_resolution_clock> start_time;
std::chrono::time_point<std::chrono::high_resolution_clock> end_time;

float softmax_part1(vector<float> input, int max_pos) {
    start_time = high_resolution_clock::now();
    float max_val = input[0];
    for (int i = 1; i < max_pos; i++)
        if (input[i] > max_val)
            max_val = input[i];
    end_time = high_resolution_clock::now();

    return max_val;
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

            auto res = softmax_part1(inp1, max_pos);
            cout << res << endl;
            time += duration_cast<microseconds>(end_time - start_time).count();
        }
        times.push_back(time);
    }


    cout << "Execution Time: " << average(times) / 1000.0 << " ms +/-" << stdiv(times) / 1000.0 << endl;
    return 0;
}
