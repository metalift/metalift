#include <iostream>
#include <vector>
#include <chrono>

#include "utils.h"

using namespace std;
using namespace std::chrono;

vector<vector<float>> color_dodge_8(vector<vector<float>> base, vector<vector<float>> active) {
    vector<vector<float>> out;
    int m = base.size();
    int n = base[0].size();
    for (int row = 0; row < m; row++) {
        vector<float> row_vec;
        for (int col = 0; col < n; col++) {
            float pixel;
            if (active[row][col] == 255)
                pixel = 255;
            else
                pixel = base[row][col] / (255 - active[row][col]);
            row_vec.push_back(pixel);
        }
        out.push_back(row_vec);
    }
    return out;
}


int main() {
    mat_timer(&color_dodge_8);
    return 0;
}