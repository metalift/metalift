#include <vector>
using namespace std;

vector<int> conv_1d(vector<int> input, vector<int> filter, int W, int W_f) {
    vector<int> output;
    for (int w = 0; w < W; w++) {
        int acc = 0;
        for (int f = 0; f < W_f; f++) {
            acc += input[w + f] * filter[f];
        }
        output.push_back(acc);
    }
    return output;
}
