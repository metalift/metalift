#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;


vector<int32_t> ol_l2_cpu2(int n, vector<int32_t> pred, vector<int32_t> truth) {
    int i;
    vector<int32_t> delta;
    for (i = 0; i < n; ++i) {
        int32_t diff = truth[i] - pred[i];
        delta.push_back(diff);
    }
    return delta;
}
