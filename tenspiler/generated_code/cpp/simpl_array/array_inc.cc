#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;


vector<int32_t> array_inc(vector<int32_t> arr, int n) {
    vector<int32_t> out;
    for (int i = 0; i < n; ++i) {
        out.push_back(arr[i] + 1);
    }
    return out;
}
