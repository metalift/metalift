#include <iostream>
#include <vector>
#include <chrono>

#include "utils.h"

using namespace std;
using namespace std::chrono;

vector<float> normal_blend_8(vector<float> base, vector<float> active, float opacity)
{
  vector<float> out;
  for (int i = 0; i < base.size(); ++i)
    out.push_back(opacity * active[i] + (255 - opacity) * base[i]);

  return out;
}

int main() {
  vec_timer(&normal_blend_8);
  return 0;
}