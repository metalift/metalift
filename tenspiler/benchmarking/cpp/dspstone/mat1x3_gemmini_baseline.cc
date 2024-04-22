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


vector<int32_t> mat1x3(int N, vector<vector<int32_t>> h, vector<int32_t> x) {
    start_time_k = high_resolution_clock::now();
    vector<int32_t> y;
    for (int i = 0; i < N; i++) {
        int32_t sum = 0;
        for (int f = 0; f < N; f++) {
            sum += h[i][f] * x[f];
        }
        y.push_back(sum);
    }
    end_time_k = high_resolution_clock::now();
    return y;
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
            vector<vector<int32_t>> base = random_matrix_int(500, 500); 
            vector<vector<int32_t>> active = random_matrix_int(500, 500); 
            vector<int32_t> active_f = flatten_int32(active); 

            int M = base.size();
            int N = base[0].size();
            if (M < N) {
                N = M;
            }
            
            auto start_time = high_resolution_clock::now();
            mat1x3(N, base, active_f);
            auto end_time = high_resolution_clock::now();
            
            time += duration_cast<microseconds>(end_time - start_time).count();
            time_k += duration_cast<microseconds>(end_time_k - start_time_k).count();
        
        }
        times.push_back(time);
        times_k.push_back(time_k);
    }
    cout << "mat1x3_gemmini_baseline" << endl;
    cout << average(times) / 1000.0 << " " << stdiv(times) / 1000.0 << endl;
    cout << average(times_k) / 1000.0 << " " << stdiv(times_k) / 1000.0 << endl;

}


