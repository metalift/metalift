#include <vector>
using namespace std;

int softmax_part1(vector<int> input, int max_pos) {
    int max_val = input[0];
    for (int i = 1; i < max_pos; i++)
        if (input[i] > max_val)
            max_val = input[i];
    return max_val;
}
// def softmax_part1_ps(input max_pos softmax_part1_rv)
// softmax_part1_rv == reduce_max(list_take(input, max_pos))
