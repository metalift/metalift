#include <iostream>
#include <vector>
#include <chrono>

#include "utils.h"

using namespace std;
using namespace std::chrono;

vector<vector<float>> overlay_blend_8(vector<vector<float>> base, vector<vector<float>> active) {
    vector<vector<float>> out;
    int m = base.size();
    int n = base[0].size();
    for (int row = 0; row < m; row++) {
        vector<float> row_vec;
        for (int col = 0; col < n; col++) {
            float pixel;
			if (base[row][col] >= 128)
                pixel = 2 * base[row][col] + base[row][col] - 2 * base[row][col] * base[row][col] / 255 - 255;
			else
                pixel = 2 * base[row][col] * base[row][col] / 255;
			row_vec.push_back(pixel);
        }
        out.push_back(row_vec);
    }
    return out;
}


int main() {
    mat_timer(&overlay_blend_8);
    return 0;
}