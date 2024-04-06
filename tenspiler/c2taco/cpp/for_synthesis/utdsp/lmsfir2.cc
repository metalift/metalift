#include <vector>
using namespace std;

vector<int> lmsfir2(int NTAPS, vector<int> input, vector<int> coefficient, int error) {
    vector<int> out;
    for (int i = 0; i < NTAPS - 1; ++i) {
        int curr = coefficient[i] + input[i] * error;
        out.push_back(curr);
    }
    return out;
}

// vec_elemwise_add(vec_slice(coefficient, 0, NTAPS - 1), vec_scalar_mul(error, vec_slice(input, 0, NTAPS - 1)))
