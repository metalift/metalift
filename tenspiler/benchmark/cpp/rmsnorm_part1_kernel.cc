#include <iostream>
#include <vector>
#include <chrono>
#include <tuple>

#include "utils.h"

using namespace std;
using namespace std::chrono;

std::chrono::time_point<std::chrono::high_resolution_clock> start_time;
std::chrono::time_point<std::chrono::high_resolution_clock> end_time;

float rmsnorm_part1(vector<float> input, vector<float> weight) {
    start_time = high_resolution_clock::now();
    float ss = 0;
    for (int i = 0; i < input.size(); i++)
        ss += input[i] * input[i];
    end_time = high_resolution_clock::now();

    return ss;
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

            auto res = rmsnorm_part1(inp2, inp1);
            cout << res << endl;
            time += duration_cast<microseconds>(end_time - start_time).count();
        }
        times.push_back(time);

    }


    cout << "Execution Time: " << average(times) / 1000.0 << " ms +/-" << stdiv(times) / 1000.0 << endl;
    return 0;
}
