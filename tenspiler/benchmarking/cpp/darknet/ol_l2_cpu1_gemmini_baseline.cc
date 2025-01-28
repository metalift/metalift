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


vector<int32_t> ol_l2_cpu1(int n, vector<int32_t> pred, vector<int32_t> truth) {
    start_time_k = high_resolution_clock::now();
    int i;
    vector<int32_t> error;
    for (i = 0; i < n; ++i) {
        int32_t diff = truth[i] - pred[i];
        error.push_back(diff * diff);
    }
    end_time_k = high_resolution_clock::now();
    return error;
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

            vector<int32_t> base_f = random_vector_int(488);
            vector<int32_t> active_f = random_vector_int(488);
            int n = base_f.size();
            auto start_time = high_resolution_clock::now();
            ol_l2_cpu1(n, base_f, active_f);
            auto end_time = high_resolution_clock::now();

            time += duration_cast<microseconds>(end_time - start_time).count();
            time_k += duration_cast<microseconds>(end_time_k - start_time_k).count();

        }
        times.push_back(time);
        times_k.push_back(time_k);
    }

    cout << "ol_l2_cpu1_gemmini_baseline" << endl;
    cout << average(times) / 1000.0 << " " << stdiv(times) / 1000.0 << endl;
    cout << average(times_k) / 1000.0 << " " << stdiv(times_k) / 1000.0 << endl;

}
