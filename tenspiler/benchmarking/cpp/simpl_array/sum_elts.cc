#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;


int32_t sum_elts(vector<int32_t> arr, int n) {
    int32_t sum = 0;
    for (int i = 0; i < n; ++i) {
        sum += arr[i];
    }
    return sum;
}
