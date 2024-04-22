
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

vector<int32_t> gemv(int M, int N, vector<vector<int32_t>> A, vector<int32_t> x) {
    start_time_k = high_resolution_clock::now();
    vector<int32_t> y;
    for (int i = 0; i < M; ++i) {
        int sum = 0;
        for (int j = 0; j < N; ++j) {
            sum += A[i][j] * x[j];
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

        vector<int32_t> active_f = random_vector_int(500*500); 

        int M = base.size();
        int N = base[0].size();
        std::vector<int32_t> active_f_sub(active_f.begin(), active_f.begin() + N);
        
        auto start_time = high_resolution_clock::now();
        auto res2 = gemv(M, N, base, active_f_sub);
        auto end_time = high_resolution_clock::now();
        cout << res2[0] << endl;
        time += duration_cast<microseconds>(end_time - start_time).count();
        time_k += duration_cast<microseconds>(end_time_k - start_time_k).count();
    
    }
    times.push_back(time);
    times_k.push_back(time_k);
  }

  cout << "gemv_gemmini_baseline" << endl;
  cout << average(times) / 1000.0 << " " << stdiv(times) / 1000.0 << endl;
  cout << average(times_k) / 1000.0 << " " << stdiv(times_k) / 1000.0 << endl;
  return 0;
}

