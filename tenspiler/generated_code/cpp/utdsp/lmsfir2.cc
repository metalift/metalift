#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;


vector<int32_t> lmsfir2(int NTAPS, vector<int32_t> input, vector<int32_t> coefficient, int32_t error) {
    vector<int32_t> out;
    for (int i = 0; i < NTAPS - 1; ++i) {
        int32_t curr = coefficient[i] + input[i] * error;
        out.push_back(curr);
    }
    return out;
}
