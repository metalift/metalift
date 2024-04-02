#include <iostream>
#include <vector>
#include <chrono>

#include "utils.h"

using namespace std;
using namespace std::chrono;

vector<vector<float>> dissolve_blend_8(vector<vector<float>> base, vector<vector<float>> active, float opacity) {
    vector<vector<float>> out;
    int m = base.size();
    int n = base[0].size();
    for (int row = 0; row < m; row++) {
        vector<float> row_vec;
        for (int col = 0; col < n; col++) {
            float pixel;
            float rand_val = ((rand() % 100) + 1) / 100.0f;
            if (opacity - rand_val >= 0.0f)
                pixel = active[row][col];
            else
                pixel = base[row][col];
            row_vec.push_back(pixel);
        }
        out.push_back(row_vec);
    }
    return out;
}

int main() {
    mat_timer_float(&dissolve_blend_8);
    return 0;
}
