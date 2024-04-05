#include <vector>
using namespace std;

vector<int> vneg(vector<int> arr, int n) {
    vector<int> out;
    for (int i = 0; i < n; ++i) {
        out.push_back(-arr[i]);
    }
    return out;
}

// scalar_vec_sub(0, vec_slice(arr, 0, n))
