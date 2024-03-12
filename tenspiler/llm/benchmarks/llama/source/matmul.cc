#include <vector>
using namespace std;

vector<int> matmul(vector<vector<int>> weight, vector<int> input) {
    vector<int> output;
    int m = weight.size();
    int n = input.size();
    for (int row = 0; row < m; row++) {
        int curr = 0;
        for (int col = 0; col < n; col++) {
            curr += weight[row][col] * input[col];
        }
        output.push_back(curr);
    }
    return output;
}
