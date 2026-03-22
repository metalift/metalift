#include <vector>
using namespace std;

// TODO(jie): change function name
vector<vector<int>> conv_1d_rosette(
    vector<vector<int>> input,    // [C][W]
    vector<vector<int>> filter)   // [C][3]
{
    vector<vector<int>> output;
    int C = input.size();
    int W = input[0].size();

    for (int c = 0; c < C; c++) {                  // loop 1: channels
        vector<int> row_vec;
        for (int w = 0; w < W; w++) {
            int val = 0;
            if (w + 2 < W) {
                val = input[c][w + 0] * filter[c][0]
                    + input[c][w + 1] * filter[c][1]
                    + input[c][w + 2] * filter[c][2];
            }
            row_vec.push_back(val);
        }
        output.push_back(row_vec);
    }
    return output;
}
