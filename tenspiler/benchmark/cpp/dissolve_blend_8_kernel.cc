#include <iostream>
#include <vector>
#include <chrono>

#include "utils.h"

#include <string>
#include <dirent.h>
#include <sys/types.h>
#include <opencv2/opencv.hpp>
#include <opencv2/highgui/highgui.hpp>
#include <opencv2/highgui/highgui_c.h>
using namespace cv;
#include "H5Cpp.h"
#include <H5public.h>

using namespace std;
using namespace std::chrono;

std::chrono::time_point<std::chrono::high_resolution_clock> start_time;
std::chrono::time_point<std::chrono::high_resolution_clock> end_time;

vector<vector<float>>  dissolve_blend_8_kernel(vector<vector<float>> base, vector<vector<float>> active, float opacity) {
    vector<vector<float>> out;
    int m = base.size();
    int n = base[0].size();
    start_time = high_resolution_clock::now();
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
            vector<vector<uint8_t>> base_int = res[0];
            vector<vector<uint8_t>> active_int = res[1];

            vector<vector<float>> base(base_int.size(), vector<float>());

            for (size_t i = 0; i < base_int.size(); ++i) {
                base[i].resize(base_int[i].size());
                for (size_t j = 0; j < base_int[i].size(); ++j) {
                    base[i][j] = static_cast<float>(base_int[i][j]);
                }
            }

            vector<vector<float>> active(active_int.size(), vector<float>());

            for (size_t i = 0; i < active_int.size(); ++i) {
                active[i].resize(active_int[i].size());
                for (size_t j = 0; j < active_int[i].size(); ++j) {
                    active[i][j] = static_cast<float>(active_int[i][j]);
                }
            }

            float opacity = random_float();

            dissolve_blend_8_kernel(base, active, opacity);
            time += duration_cast<microseconds>(end_time - start_time).count();
        }
        times.push_back(time);
    }


    cout << "Execution Time: " << average(times) / 1000.0 << " ms +/-" << stdiv(times) / 1000.0 << endl;
    return 0;
}
