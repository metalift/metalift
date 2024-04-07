#include <vector>
using namespace std;

vector<int> diveq_sca(vector<int> a, int b, int n) {
    vector<int> out;
    for (int i = 0; i < n; ++i) {
        out.push_back(a[i] / b);
    }
    return out;
}

// vec_scalar_div(b, vec_slice(a, 0, n))
