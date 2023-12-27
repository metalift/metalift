#include <vector>
using namespace std;

int softmax_part3(vector<int> output, int max_pos) {
    int sum = 0;
    for (int i = 0; i < max_pos; i++) {
        sum += output[i];
    }
    return sum;
}
// def softmax_part3_ps(output max_pos softmax_part3_rv)
// softmax_part3_rv == reduce_sum(list_take(output, max_pos))