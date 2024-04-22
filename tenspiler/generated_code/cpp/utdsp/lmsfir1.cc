#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;

int32_t lmsfir1(int NTAPS, vector<int32_t> input, vector<int32_t> coefficient) {
    int32_t sum = 0;
    for (int i = 0; i < NTAPS; ++i) {
        sum += input[i] * coefficient[i];
    }
    return sum;
}
