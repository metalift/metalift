#include <vector>
using namespace std;

vector<int> vsub(vector<int> a, vector<int> b, int n) {
    vector<int> out;
    for (int i = 0; i < n; ++i) {
        out.push_back(a[i] - b[i]);
    }
    return out;
}

// vec_elemwise_sub(vec_slice(a, 0, n), vec_slice(b, 0, n))
