#include <vector>
using namespace std;

int softmax_part1(vector<int> input, int max_pos) {
    // int max_val = input[0];
    int max_val = 0;
    for (int i = 0; i < input.size(); i++)
        if (input[i] > max_val)
            max_val = input[i];
    return max_val;
}