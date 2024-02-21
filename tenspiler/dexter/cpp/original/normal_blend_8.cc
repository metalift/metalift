#include <vector>
using namespace std;

vector<uint8_t> normal_blend_8(vector<uint8_t> base, vector<uint8_t> active, uint8_t opacity)
{
  vector<uint8_t> out;
  for (int i = 0; i < base.size(); ++i)
    out.push_back(opacity * active[i] + (255 - opacity) * base[i]);

  return out;
}
// def normal_blend_8_ps(base active opacity normal_blend_8_rv)
// normal_blend_8_rv == vec_elemwise_add(vec_scalar_mul(opacity, active), vec_scalar_mul((255 - opacity), base))
