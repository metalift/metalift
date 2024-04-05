#include <vector>
using namespace std;

vector<int> ol_l2_cpu1(int n, vector<int> pred, vector<int> truth) {
    int i;
    vector<int> error;
    for (i = 0; i < n; ++i) {
        int diff = truth[i] - pred[i];
        error.push_back(diff * diff);
    }
    return error;
}

// vec_elemwise_mul(vec_elemwise_sub(vec_slice(truth, 0, n), vec_slice(pred, 0, n)), vec_elemwise_sub(vec_slice(truth, 0, n), vec_slice(pred, 0, n)))
