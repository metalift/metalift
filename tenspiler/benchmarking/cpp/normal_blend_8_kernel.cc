#include <iostream>
#include <vector>
#include <chrono>

#include "utils.h"

using namespace std;
using namespace std::chrono;

std::chrono::time_point<std::chrono::high_resolution_clock> start_time;
std::chrono::time_point<std::chrono::high_resolution_clock> end_time;

vector<uint8_t> normal_blend_8_kernel(vector<uint8_t> base, vector<uint8_t> active, uint8_t opacity) {
  vector<uint8_t> out;
  start_time = high_resolution_clock::now();
  for (int i = 0; i < base.size(); ++i)
    out.push_back(opacity * active[i] + (255 - opacity) * base[i]);
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
            vector<uint8_t> base_f = flatten_int(base);
            vector<vector<uint8_t>> active = res[1];
            vector<uint8_t> active_f = flatten_int(active);
            uint8_t opacity = static_cast<uint8_t>(random_float());

            normal_blend_8_kernel(base_f, active_f, opacity);

            time += duration_cast<microseconds>(end_time - start_time).count();
        }
        times.push_back(time);
    }


    cout << "Execution Time: " << average(times) / 1000.0 << " ms +/-" << stdiv(times) / 1000.0 << endl;
    return 0;
}
