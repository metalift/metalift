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

int32_t mag_array(vector<int32_t> a, int n) {
    start_time_k = high_resolution_clock::now();
    int i;
    int32_t sum = 0;
    for(i = 0; i < n; ++i){
        sum += a[i] * a[i];
    }

    end_time_k = high_resolution_clock::now();
    return sum;
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

            vector<int32_t> base_f = flatten_int32(base);

            int n = base_f.size();

            auto start_time = high_resolution_clock::now();
            auto result = mag_array(base_f, n);
            auto end_time = high_resolution_clock::now();
            cout << result << endl;
            time += duration_cast<microseconds>(end_time - start_time).count();
            time_k += duration_cast<microseconds>(end_time_k - start_time_k).count();

        }
        times.push_back(time);
        times_k.push_back(time_k);
    }

    cout << "mag_array" << endl;
    cout << average(times) / 1000.0 << " " << stdiv(times) / 1000.0 << endl;
    cout << average(times_k) / 1000.0 << " " << stdiv(times_k) / 1000.0 << endl;

}
