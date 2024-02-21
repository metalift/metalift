#include <vector>
using namespace std;

vector<int> normal_blend_f(vector<int> base, vector<int> active, int opacity)
{
  vector<int> out;
  for (int i = 0; i < base.size(); ++i)
    out.push_back(opacity * active[i] + (1 - opacity) * base[i]);
  return out;
}
// def normal_blend_f_ps(base active opacity normal_blend_f_rv)
// normal_blend_f_rv == vec_elemwise_add(vec_scalar_mul(opacity, active), vec_scalar_mul((1 - opacity), base))
