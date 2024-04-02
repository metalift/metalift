#include <iostream>
#include <vector>
#include <chrono>

#include "utils.h"

using namespace std;
using namespace std::chrono;

std::chrono::time_point<std::chrono::high_resolution_clock> start_time;
std::chrono::time_point<std::chrono::high_resolution_clock> end_time;

vector<float> normal_blend_f_kernel(vector<float> base, vector<float> active, float opacity)
{
  vector<float> out;
  start_time = high_resolution_clock::now();
  for (int i = 0; i < base.size(); ++i)
    out.push_back(opacity * active[i] + (1 - opacity) * base[i]);
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

            vector<float> base_f = flatten(base);
            vector<float> active_f = flatten(active);
            float opacity = random_float();

            normal_blend_f_kernel(base_f, active_f, opacity);

            time += duration_cast<microseconds>(end_time - start_time).count();
        }
        times.push_back(time);
    }


    cout << "Execution Time: " << average(times) / 1000.0 << " ms +/-" << stdiv(times) / 1000.0 << endl;
    return 0;
}
