#include <vector>
using namespace std;

vector<int> ol_l2_cpu2(int n, vector<int> pred, vector<int> truth) {
    int i;
    vector<int> delta;
    for (i = 0; i < n; ++i) {
        int diff = truth[i] - pred[i];
        delta.push_back(diff);
    }
    return delta;
}
// vec_elemwise_sub(vec_slice(truth, 0, n), vec_slice(pred, 0, n))
