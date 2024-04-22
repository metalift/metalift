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


int len_sq(vector<int32_t> arr, int n) {
    start_time_k = high_resolution_clock::now();
    int32_t l = 0;
    for (int i = 0; i < n; ++i) {
        l += arr[i] * arr[i];
    }
    end_time_k = high_resolution_clock::now();
    return l;
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
            
            vector<int32_t> base_f = random_vector_int(122); 
            
            int n = base_f.size();

            auto start_time = high_resolution_clock::now();
            auto result = len_sq(base_f, n);
            auto end_time = high_resolution_clock::now();
            cout << result << endl;
            time += duration_cast<microseconds>(end_time - start_time).count();
            time_k += duration_cast<microseconds>(end_time_k - start_time_k).count();
        
        }
        times.push_back(time);
        times_k.push_back(time_k);
    }


    cout << "len_sq_baseline" << endl;
    cout << average(times) / 1000.0 << " " << stdiv(times) / 1000.0 << endl;
    cout << average(times_k) / 1000.0 << " " << stdiv(times_k) / 1000.0 << endl;

}
