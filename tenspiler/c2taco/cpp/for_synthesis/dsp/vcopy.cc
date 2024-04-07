#include <vector>
using namespace std;

vector<int> vcopy(vector<int> a, int n) {
    vector<int> out;
    for (int i = 0; i < n; ++i) {
        out.push_back(a[i]);
    }
    return out;
}

// vec_slice(a, 0, n)
