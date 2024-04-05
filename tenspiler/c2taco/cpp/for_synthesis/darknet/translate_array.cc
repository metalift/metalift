#include <vector>
using namespace std;

vector<int> translate_array(vector<int> a, int n, int s)
{
    int i;
    vector<int> out;
    for (i = 0; i < n; ++i) {
        out.push_back(a[i] + s);
    }
    return out;
}

// vec_scalar_add(s, vec_slice(a, 0, n))
