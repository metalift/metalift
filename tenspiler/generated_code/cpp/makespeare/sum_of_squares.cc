#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;


int32_t sum_of_squares(vector<int32_t> arr, int n) {
    int32_t sum = 0;
    for (int i = 0; i < n; ++i) {
        sum += arr[i] * arr[i];
    }
    return sum;
}
