#include <vector>
using namespace std;

int integer_sqrt(int x) { return x; }

vector<int> rmsnorm_part2(vector<int> input, vector<int> weight, int ss) {
    vector<int> output;
    int size = input.size();
    for (int i = 0; i < input.size(); i++) {
        output.push_back((1 / integer_sqrt(ss / size + 1)) * input[i] * weight[i]);
    }
    return output;
}
