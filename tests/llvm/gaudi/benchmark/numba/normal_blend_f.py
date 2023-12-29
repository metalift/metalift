from numba import njit

@njit
def normal_blend_f(base, active, opacity: int):
  output = []
  for i in range(len(base)):
    output.append(opacity * active[i] + (1 - opacity) * base[i])
  return output