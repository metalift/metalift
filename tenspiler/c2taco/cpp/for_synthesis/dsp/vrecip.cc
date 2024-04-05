#include <vector>
using namespace std;

vector<int> vrecip(vector<int> arr, int n) {
    vector<int> out;
    for (int i = 0; i < n; ++i) {
        out.push_back(1 / arr[i]);
    }
    return out;
}

// scalar_vec_div(1, vec_slice(arr, 0, n))
