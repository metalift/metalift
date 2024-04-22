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

vector<int32_t> diveq(vector<int32_t> a, vector<int32_t> b, int n) {
    start_time_k = high_resolution_clock::now();
    vector<int32_t> out;
    for (int i = 0; i < n; ++i) {
        out.push_back(a[i] / b[i]);
    }
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
            std::array<vector<vector<int32_t>>,2> res = get_base_active_int(j);
            vector<vector<int32_t>> base = res[0]; 
            vector<vector<int32_t>> active = res[1]; 
            
            vector<int32_t> base_f = flatten_int32(base); 
            vector<int32_t> active_f = flatten_int32(active); 

            if (std::find(active_f.begin(), active_f.end(), 0) != active_f.end()) {
                for (auto& value : active_f) {
                    if (value == 0) {
                        value = 1;
                    }
                }
            }
            
            int n = base_f.size();

            auto start_time = high_resolution_clock::now();
            diveq(base_f, active_f, n);
            auto end_time = high_resolution_clock::now();
            
            time += duration_cast<microseconds>(end_time - start_time).count();
            time_k += duration_cast<microseconds>(end_time_k - start_time_k).count();
        
        }
        times.push_back(time);
        times_k.push_back(time_k);
    }
    cout << "diveq" << endl;
    cout << average(times) / 1000.0 << " " << stdiv(times) / 1000.0 << endl;
    cout << average(times_k) / 1000.0 << " " << stdiv(times_k) / 1000.0 << endl;

}
