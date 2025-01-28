#include <iostream>
#include <vector>
#include <chrono>

#include "random.h"

using namespace std;
using namespace std::chrono;

vector<float> a = random_vector();
vector<float> b = random_vector();
float c = random_float();

vector<float> normal_blend_8(vector<float> base, vector<float> active, float opacity)
{
  vector<float> out;
  for (int i = 0; i < base.size(); ++i)
    out.push_back(opacity * active[i] + (255 - opacity) * base[i]);

  return out;
}

int main() {
    vector<long long> times;
    for (int i = 0; i < 10; i++) {
        auto start_time = high_resolution_clock::now();
        normal_blend_8(a, b, c);
        auto end_time = high_resolution_clock::now();
        auto duration = duration_cast<microseconds>(end_time - start_time);
        times.push_back(duration.count());
    }


    cout << "Execution Time: " << average(times) << " microseconds +/-" << stdiv(times) << endl;
}