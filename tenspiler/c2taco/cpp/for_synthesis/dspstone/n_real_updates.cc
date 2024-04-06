#include <vector>
using namespace std;

vector<int> n_real_updates(int N, vector<int> A, vector<int> B, vector<int> C) {
    vector<int> D;
    for (int i = 0; i < N; i++) {
        int curr = C[i] + A[i] * B[i];
        D.push_back(curr);
    }
    return D;
}

// vec_elemwise_add(vec_slice(C, 0, N), vec_elemwise_mul(vec_slice(A, 0, N), vec_slice(B, 0, N)))
