#include <iostream>
#include <vector>
#include <chrono>

#include "random.h"

using namespace std;
using namespace std::chrono;

vector<vector<float>> a = random_matrix();
vector<vector<float>> b = random_matrix();

vector<vector<float>> color_dodge_8(vector<vector<float>> base, vector<vector<float>> active) {
    vector<vector<float>> out;
    int m = base.size();
    int n = base[0].size();
    for (int row = 0; row < m; row++) {
        vector<float> row_vec;
        for (int col = 0; col < n; col++) {
            float pixel;
            if (active[row][col] == 32)
                pixel = 32;
            else
                pixel = base[row][col] / (32 - active[row][col]);
            row_vec.push_back(pixel);
        }
        out.push_back(row_vec);
    }
    return out;
}


int main() {
    auto start_time = high_resolution_clock::now();
    color_dodge_8(a, b);
    auto end_time = high_resolution_clock::now();
    auto duration = duration_cast<microseconds>(end_time - start_time);

    cout << "Execution Time: " << duration.count() << " microseconds" << endl;
}