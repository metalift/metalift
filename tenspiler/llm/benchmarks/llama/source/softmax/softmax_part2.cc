#include <vector>
using namespace std;

int integer_exp(int x) { return x; }

vector<int> softmax_part2(vector<int> input, int max_pos, int max_val) {
    vector<int> output;
    for (int i = 0; i < max_pos; i++) {
        int cur = integer_exp(input[i] - max_val);
        output.push_back(cur);
    }
    return output;
}
