#include <vector>
#include <stdio.h>
#include <stdlib.h>
using namespace std;

vector<float> normal_blend_f(vector<float> base, vector<float> active, float opacity)
{
  vector<float> out;
  for (int i = 0; i < base.size(); ++i)
    out.push_back(opacity * active[i] + (1 - opacity) * base[i]);

  return out;
}
