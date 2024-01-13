#include <vector>

std::vector<int> test(std::vector<int> in)
{
  std::vector<int> out;
  for (int i = 0; i < in.size(); ++i)
    out.push_back(in[i]);

  return out;
}
