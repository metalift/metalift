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

// matmul(matrix_col_slice(matrix_row_slice(A, 0, M), 0, N), vec_slice(x, 0, N))

int main() {
  srand(1);
  fn = glob("/tier1/ucb/imagenet10k/data/", ".*\\.jpeg$");

  vector<long long> times;
  vector<long long> times_k;
  size_t count = fn.size();
  for (int i = 0; i < 10; i++) {
      long long time = 0;
      long long time_k = 0;
      for (int j = 0; j < count; j++) {
          std::array<vector<vector<int32_t>>,2> res = get_base_active_int(j);
          vector<vector<int32_t>> base = res[0];
          vector<vector<int32_t>> active = res[1];
          vector<int32_t> active_f = flatten_int32(active);

          int M = base.size();
          int N = base[0].size();
          std::vector<int32_t> active_f_sub(active_f.begin(), active_f.begin() + N);

          auto start_time = high_resolution_clock::now();
          gemv(M, N, base, active_f_sub);
          auto end_time = high_resolution_clock::now();

          time += duration_cast<microseconds>(end_time - start_time).count();
          time_k += duration_cast<microseconds>(end_time_k - start_time_k).count();

      }
      times.push_back(time);
      times_k.push_back(time_k);
  }

  cout << average(times) / 1000.0 << " " << stdiv(times) / 1000.0 << endl;
  cout << average(times_k) / 1000.0 << " " << stdiv(times_k) / 1000.0 << endl;
}
