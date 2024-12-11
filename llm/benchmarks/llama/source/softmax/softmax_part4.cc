#include <vector>
using namespace std;

vector<int> softmax_part4(vector<int> unnormalized_output, int max_pos, int sum) {
    vector<int> output;
    for (int i = 0; i < max_pos; i++) {
        output.push_back(unnormalized_output[i] / sum);
    }
    return output;
}
