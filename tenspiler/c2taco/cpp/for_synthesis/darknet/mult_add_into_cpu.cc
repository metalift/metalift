#include <vector>
using namespace std;

vector<int> mult_add_into_cpu(int N, vector<int> X, vector<int> Y, vector<int> Z) {
    int i;
    vector<int> out;
    for(i = 0; i < N; ++i) {
        out.push_back(Z[i] + X[i] * Y[i]);
    }
    return out;
}

// vec_elemwise_add(vec_slice(Z, 0, N), vec_elemwise_mul(vec_slice(X, 0, N), vec_slice(Y, 0, N)))
