#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;


int32_t mag_array(vector<int32_t> a, int n) {
    int i;
    int32_t sum = 0;
    for(i = 0; i < n; ++i){
        sum += a[i] * a[i];
    }

    return sum;
}
