#include <iostream>
#include <vector>
#include <chrono>

#include "utils.h"

using namespace std;
using namespace std::chrono;

std::chrono::time_point<std::chrono::high_resolution_clock> start_time;
std::chrono::time_point<std::chrono::high_resolution_clock> end_time;

vector<vector<uint8_t>> overlay_blend_8_kernel(vector<vector<uint8_t>> base, vector<vector<uint8_t>> active) {
    vector<vector<uint8_t>> out;
    int m = base.size();
    int n = base[0].size();
    start_time = high_resolution_clock::now();
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
    end_time = high_resolution_clock::now();
    return out;
}


int main() {
    srand(1);
    fn = glob("./data", ".*\\.jpeg$");

    vector<long long> times;
    size_t count = fn.size();
    for (int i = 0; i < 10; i++) {
        long long time = 0;
        for (int j = 0; j < count; j++) {
            std::array<vector<vector<uint8_t>>,2> res = get_base_active(j);
            vector<vector<uint8_t>> base = res[0];
            vector<vector<uint8_t>> active = res[1];

            overlay_blend_8_kernel(base, active);

            time += duration_cast<microseconds>(end_time - start_time).count();
        }
        times.push_back(time);
    }


    cout << "Execution Time: " << average(times) / 1000.0 << " ms +/-" << stdiv(times) / 1000.0 << endl;
    return 0;
}
