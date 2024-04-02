#include <iostream>
#include <vector>
#include <chrono>

#include "utils.h"

using namespace std;
using namespace std::chrono;

vector<uint8_t> normal_blend_8(vector<uint8_t> base, vector<uint8_t> active, uint8_t opacity) {
  vector<uint8_t> out;
  for (int i = 0; i < base.size(); ++i)
    out.push_back(opacity * active[i] + (255 - opacity) * base[i]);

  return out;
}

int main() {
  vec_timer_int(&normal_blend_8);
  return 0;
}
