#include <vector>
using namespace std;

vector<vector<int>> conv_1d_smt(
    vector<vector<int>> input,    // [C][W]
    vector<vector<int>> filter)   // [C][3]
{
    vector<vector<int>> output;
    int C = input.size();
    int W = input[0].size();

    for (int c = 0; c < C; c++) {
        vector<int> row_vec;
        for (int w = 0; w < W - 2; w++) {
            row_vec.push_back(input[c][w + 0] * filter[c][0]
                + input[c][w + 1] * filter[c][1]
                + input[c][w + 2] * filter[c][2]);
        }
        output.push_back(row_vec);
    }
    return output;
}
