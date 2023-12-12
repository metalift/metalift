#include <vector>
using namespace std;

int test_sqrt(int x) { return x; }

vector<int> silu(vector<int> input, int hidden_dim) {
    vector<int> output;
    for (int i = 0; i < hidden_dim; i++) {
        int curr = 1 / (1 + test_sqrt(input[i])) * input[i];
        output.push_back(curr);
    }
    return output;
}