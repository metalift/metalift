#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;


vector<int32_t> vcopy(vector<int32_t> a, int n) {
    vector<int32_t> out;
    for (int i = 0; i < n; ++i) {
        out.push_back(a[i]);
    }
    return out;
}
