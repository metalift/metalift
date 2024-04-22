#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;


vector<int32_t> vscal(vector<int32_t> arr, int32_t v, int n) {
    vector<int32_t> out;
    for (int i = 0; i < n; ++i) {
        out.push_back(v * arr[i]);
    }
    return out;
}
