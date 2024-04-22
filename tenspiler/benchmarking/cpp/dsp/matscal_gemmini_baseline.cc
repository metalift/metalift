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

vector<vector<int32_t>> matscal(vector<vector<int32_t>> mat, int32_t val, int m, int n) {
    start_time_k = high_resolution_clock::now();
    vector<vector<int32_t>> out;
    for (int i = 0; i < m; ++i) {
        vector<int32_t> row_vec;
        for (int j = 0; j < n; ++j) {
            row_vec.push_back(mat[i][j] * val);
        }
        out.push_back(row_vec);
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
           
            vector<vector<int32_t>> base = random_matrix_int(500, 500); 
            int32_t val = rand();

            int m = base.size();
            int n = base[0].size();

            auto start_time = high_resolution_clock::now();
            matscal(base, val, m, n);
            auto end_time = high_resolution_clock::now();
            
            time += duration_cast<microseconds>(end_time - start_time).count();
            time_k += duration_cast<microseconds>(end_time_k - start_time_k).count();
        
        }
        times.push_back(time);
        times_k.push_back(time_k);
    }
    cout << "matscal_gemmini_baseline" << endl;
    cout << average(times) / 1000.0 << " " << stdiv(times) / 1000.0 << endl;
    cout << average(times_k) / 1000.0 << " " << stdiv(times_k) / 1000.0 << endl;

}

