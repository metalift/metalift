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


vector<int32_t> lmsfir2(int NTAPS, vector<int32_t> input, vector<int32_t> coefficient, int32_t error) {
    start_time_k = high_resolution_clock::now();
    vector<int32_t> out;
    for (int i = 0; i < NTAPS - 1; ++i) {
        int32_t curr = coefficient[i] + input[i] * error;
        out.push_back(curr);
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
            int32_t err = rand();

            auto start_time = high_resolution_clock::now();
            lmsfir2(N, base_f, active_f, err);
            auto end_time = high_resolution_clock::now();

            time += duration_cast<microseconds>(end_time - start_time).count();
            time_k += duration_cast<microseconds>(end_time_k - start_time_k).count();
        
        }
        times.push_back(time);
        times_k.push_back(time_k);
    }
    cout << "lmsfir2_gemmini_baseline" << endl;
    cout << average(times) / 1000.0 << " " << stdiv(times) / 1000.0 << endl;
    cout << average(times_k) / 1000.0 << " " << stdiv(times_k) / 1000.0 << endl;

}


