#include <vector>
using namespace std;

int rmsnorm_part1(vector<int> input, vector<int> weight) {
    int ss = 0;
    for (int i = 0; i < input.size(); i++)
        ss += input[i] * input[i];
    return ss;
}

