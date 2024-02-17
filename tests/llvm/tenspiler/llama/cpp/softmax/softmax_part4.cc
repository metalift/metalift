#include <vector>
using namespace std;

vector<int> softmax_part4(vector<int> unnormalized_output, int max_pos, int sum) {
    vector<int> output;
    for (int i = 0; i < max_pos; i++) {
        output.push_back(unnormalized_output[i] / sum);
    }
    return output;
}
// def softmax_part4_ps(unnormalized_output max_pos sum softmax_part4_rv)
// softmax_part4_rv == vec_scalar_div(sum, list_take(unnormalized_output, max_pos))
