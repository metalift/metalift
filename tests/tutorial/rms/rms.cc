#include <vector>
using namespace std;

int integer_sqrt(int x) { return x; }

vector<int> rmsnorm(vector<int> input, vector<int> weight) {
    vector<int> output;
    int size = input.size();

    // part 1: sum of squares
    int ss = 0;
    for (int i = 0; i < size; i++)
        ss += input[i] * input[i];

    // part 2: normalize + scale
    int inv_ss = 1 / integer_sqrt(ss / size + 1);
    for (int j = 0; j < size; j++)
        output.push_back(inv_ss * input[j] * weight[j]);

    return output;
}
