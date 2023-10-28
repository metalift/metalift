#include "list.h"

std::vector<int> normal_blend_8(std::vector<int> base, std::vector<int> active, int opacity) 
{
  std::vector<int> out;
  for (int i = 0; i < base.size(); ++i)
    out.push_back(opacity * active[i] + (255 - opacity) * base[i]);

  return out;
}