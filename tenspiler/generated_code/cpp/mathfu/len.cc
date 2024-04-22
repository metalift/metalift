#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;


int32_t len(vector<int32_t> arr, int n) {
    int32_t l = 0;
    for (int i = 0; i < n; ++i) {
        l += arr[i] * arr[i];
    }
    return l;
}
