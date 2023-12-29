from numba import njit

@njit
def normal_blend_8(base, active, opacity):
  output = []
  for i in range(len(base)):
    output.append(opacity * active[i] + (255 - opacity) * base[i])
  return output