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


vector<int32_t> n_real_updates(int N, vector<int32_t> A, vector<int32_t> B, vector<int32_t> C) {
    start_time_k = high_resolution_clock::now();
    vector<int32_t> D;
    for (int i = 0; i < N; i++) {
        int32_t curr = C[i] + A[i] * B[i];
        D.push_back(curr);
    }
    end_time_k = high_resolution_clock::now();
    return D;
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
            std::array<vector<vector<int32_t>>,2> res = get_base_active_int(j);
            vector<vector<int32_t>> base = res[0]; 
            vector<vector<int32_t>> active = res[1]; 

            vector<int32_t> base_f = flatten_int32(base); 
            vector<int32_t> active_f = flatten_int32(active); 

            int N = base_f.size();
            vector<int32_t> rand_f = random_vector_int(N); 

            auto start_time = high_resolution_clock::now();
            n_real_updates(N, base_f, active_f, rand_f);
            auto end_time = high_resolution_clock::now();
            
            time += duration_cast<microseconds>(end_time - start_time).count();
            time_k += duration_cast<microseconds>(end_time_k - start_time_k).count();
        
        }
        times.push_back(time);
        times_k.push_back(time_k);
    }
    cout << "n_real_updates" << endl;
    cout << average(times) / 1000.0 << " " << stdiv(times) / 1000.0 << endl;
    cout << average(times_k) / 1000.0 << " " << stdiv(times_k) / 1000.0 << endl;

}

