#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;


vector<vector<uint8_t>> overlay_blend_8(vector<vector<uint8_t>> base, vector<vector<uint8_t>> active) {
    vector<vector<uint8_t>> out;
    int m = base.size();
    int n = base[0].size();
    for (int row = 0; row < m; row++) {
        vector<uint8_t> row_vec;
        for (int col = 0; col < n; col++) {
            uint8_t pixel;
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
