#include "list.h"
#include <cmath>
#include <tuple>

int silu(int x) {
  return x / (1 + exp(-x));
}

std::vector<int> activation_kernels(std::vector<int> x, std::vector<int> y) 
{
  std::vector<int> out;
  for (int i = 0; i < x.size(); ++i)
    out.push_back(silu(x[i]) * y[i]);

  return out;
}

int layernorm_kernels_1(std::vector<int> input, std::vector<int> weight, int epsilon, int hidden_size)
{
  int variance = 0;
  for (int i = 0; i < input.size(); i++)
    variance += input[i] * input[i];
  return variance;
}

std::vector<int> layernorm_kernels_2(std::vector<int> input, std::vector<int> weight, int epsilon, int hidden_size, int variance)
{
  int s_variance = variance + epsilon;
  std::vector<int> out;
  for (int i = 0; i < input.size(); i++)
    out.push_back((input[i] * s_variance) * weight[i]);

  return out;
}

std::tuple<int, int> get_rotary_embedding(
  std::vector<int> input,
  std::vector<int> cos_cache,
  std::vector<int> sin_cache,
  int rot_offset,
  int embed_dim,
  bool is_neox)
{
  int x_index, y_index;
  int cos, sin;
  if (is_neox) {
    x_index = rot_offset;
    y_index = embed_dim + rot_offset;
    cos = cos_cache[x_index];
    sin = sin_cache[x_index];
  } else {
    x_index = 2 * rot_offset;
    y_index = 2 * rot_offset + 1;
    cos = cos_cache[x_index / 2];
    sin = sin_cache[x_index / 2];
  }
  int x = input[x_index];
  int y = input[y_index];
  return {x * cos - y * sin, y * cos + x * sin};
}

// TODO: ???
std::vector<int> rotary_embedding(
  std::vector<int> input
)
{
  return {};
}