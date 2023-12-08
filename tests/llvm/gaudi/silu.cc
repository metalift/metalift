#include <vector>
using namespace std;

int test_sqrt(int x) { return x; }

vector<int> silu(vector<int> input, int hidden_dim) {
    vector<int> output;
    for (int i = 0; i < hidden_dim; i++) {
        int cons = 1 / (1 + test_sqrt(input[i]));
        output.push_back(cons * input[i]);
    }
    return output;
}