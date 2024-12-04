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

vector<float> normal_blend_f(vector<float> base, vector<float> active, float opacity)
{
    start_time_k = high_resolution_clock::now();
    vector<float> out;
    for (int i = 0; i < base.size(); ++i)
        out.push_back(opacity * active[i] + (1 - opacity) * base[i]);
    end_time_k = high_resolution_clock::now();
    return out;
}

int main() {
    srand(1);

    vector<long long> times;
    vector<long long> times_k;
    size_t count = 10000;
    for (int i = 0; i < 10; i++) {
        long long time = 0;
        long long time_k = 0;
        for (int j = 0; j < count; j++) {

            vector<float> base_f = random_vector(488);
            vector<float> active_f = random_vector(488);
            float opacity = random_float();

            auto start_time = high_resolution_clock::now();
            normal_blend_f(base_f, active_f, opacity);
            auto end_time = high_resolution_clock::now();

            time += duration_cast<microseconds>(end_time - start_time).count();
            time_k += duration_cast<microseconds>(end_time_k - start_time_k).count();
        }
        times.push_back(time);
        times_k.push_back(time_k);
    }


    cout << "normal_blend_f_gemmini_baseline" << endl;
    cout << average(times) / 1000.0 << " " << stdiv(times) / 1000.0 << endl;
    cout << average(times_k) / 1000.0 << " " << stdiv(times_k) / 1000.0 << endl;
    return 0;
}
