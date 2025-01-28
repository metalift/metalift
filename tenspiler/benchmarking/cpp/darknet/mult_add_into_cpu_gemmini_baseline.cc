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

vector<int32_t> mult_add_into_cpu(int N, vector<int32_t> X, vector<int32_t> Y, vector<int32_t> Z) {
    start_time_k = high_resolution_clock::now();
    int i;
    vector<int32_t> out;
    for(i = 0; i < N; ++i) {
        out.push_back(Z[i] + X[i] * Y[i]);
    }
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
            vector<int32_t> base_f = random_vector_int(488);
            vector<int32_t> active_f = random_vector_int(488);

            int N = base_f.size();
            vector<int32_t> rand_f = random_vector_int(N);

            auto start_time = high_resolution_clock::now();
            mult_add_into_cpu(N, base_f, active_f, rand_f);
            auto end_time = high_resolution_clock::now();

            time += duration_cast<microseconds>(end_time - start_time).count();
            time_k += duration_cast<microseconds>(end_time_k - start_time_k).count();

        }
        times.push_back(time);
        times_k.push_back(time_k);
    }

    cout << "mult_add_into_cpu_gemmini_baseline" << endl;
    cout << average(times) / 1000.0 << " " << stdiv(times) / 1000.0 << endl;
    cout << average(times_k) / 1000.0 << " " << stdiv(times_k) / 1000.0 << endl;

}
