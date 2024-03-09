#include <vector>
using namespace std;

int integer_sqrt(int x) { return x; }

vector<int> rmsnorm_part2(vector<int> input, vector<int> weight, int ss) {
    vector<int> output;
    int size = input.size();
    int inv_ss = 1 / integer_sqrt(ss / size + 1);
    for (int i = 0; i < input.size(); i++)
        output.push_back(inv_ss * input[i] * weight[i]);
    return output;
}
