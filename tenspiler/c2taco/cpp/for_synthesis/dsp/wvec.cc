#include <vector>
using namespace std;

vector<int> wvec(vector<int> a, vector<int> b, int m, int n) {
    vector<int> out;
    for (int i = 0; i < n; ++i) {
        out.push_back(m * a[i] + b[i]);
    }
    return out;
}

// vec_elemwise_add(vec_scalar_mul(m, vec_slice(a, 0, n)), vec_slice(b, 0, n))
