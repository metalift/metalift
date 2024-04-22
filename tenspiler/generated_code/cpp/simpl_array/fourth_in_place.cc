#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;


vector<int32_t> fourth_in_place(vector<int32_t> arr, int n) {
    vector<int32_t> out;
    for (int i = 0; i < n; ++i) {
        int32_t sq = arr[i] * arr[i];
        int32_t fourth = sq * sq;
        out.push_back(fourth);
    }
    return out;
}
