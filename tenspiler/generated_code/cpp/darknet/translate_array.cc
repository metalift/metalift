#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;


vector<int32_t> translate_array(vector<int32_t> a, int n, int32_t s)
{
    int i;
    vector<int32_t> out;
    for (i = 0; i < n; ++i) {
        out.push_back(a[i] + s);
    }
    return out;
}
