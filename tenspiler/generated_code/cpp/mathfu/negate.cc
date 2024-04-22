#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;


namespace mylib {
    vector<int32_t> negate(vector<int32_t> arr, int n) {
        start_time_k = high_resolution_clock::now();
        vector<int32_t> out;
        for (int i = 0; i < n; ++i) {
            out.push_back(-arr[i]);
        }
        end_time_k = high_resolution_clock::now();
    return out;
    }
}
