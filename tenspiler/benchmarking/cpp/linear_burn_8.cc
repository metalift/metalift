#include <iostream>
#include <vector>
#include <chrono>

#include "utils.h"

using namespace std;
using namespace std::chrono;

vector<vector<uint8_t>> linear_burn_8(vector<vector<uint8_t>> base, vector<vector<uint8_t>> active) {
    vector<vector<uint8_t>> out;
    int m = base.size();
    int n = base[0].size();
    for (int row = 0; row < m; row++) {
        vector<uint8_t> row_vec;
        for (int col = 0; col < n; col++) {
            uint8_t pixel = (base[row][col] + active[row][col]) - 255;
            row_vec.push_back(pixel);
        }
        out.push_back(row_vec);
    }
    return out;
}


int main() {
    mat_timer(&linear_burn_8);
    return 0;
}
