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

vector<uint8_t> normal_blend_8(vector<uint8_t> base, vector<uint8_t> active, uint8_t opacity) {
    start_time_k = high_resolution_clock::now();
    vector<uint8_t> out;
    for (int i = 0; i < base.size(); ++i)
        out.push_back(opacity * active[i] + (255 - opacity) * base[i]);
    end_time_k = high_resolution_clock::now();
    return out;
}

int main() {
    srand(1);
    fn = glob("./data/", ".*\\.jpeg$");

    vector<long long> times;
    vector<long long> times_k;
    size_t count = fn.size();
    for (int i = 0; i < 10; i++) {
        long long time = 0;
        long long time_k = 0;
        for (int j = 0; j < count; j++) {
            std::array<vector<vector<uint8_t>>,2> res = get_base_active(j);
            vector<vector<uint8_t>> base = res[0];
            vector<uint8_t> base_f = flatten_int(base);
            vector<vector<uint8_t>> active = res[1];
            vector<uint8_t> active_f = flatten_int(active);
            uint8_t opacity = random_grayscale();

            auto start_time = high_resolution_clock::now();
            normal_blend_8(base_f, active_f, opacity);
            auto end_time = high_resolution_clock::now();

            time += duration_cast<microseconds>(end_time - start_time).count();
            time_k += duration_cast<microseconds>(end_time_k - start_time_k).count();
        }
        times.push_back(time);
        times_k.push_back(time_k);
    }

    cout << "normal_blend_8" << endl;
    cout << average(times) / 1000.0 << " " << stdiv(times) / 1000.0 << endl;
    cout << average(times_k) / 1000.0 << " " << stdiv(times_k) / 1000.0 << endl;
    return 0;
}
