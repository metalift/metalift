from numba import njit

@njit
def overlay_blend_8(base, active):
  output = []
  m = len(base)
  n = len(base[0])
  for i in range(m):
    curr_row = []
    for j in range(n):
      if base[i][j] >= 128:
        pixel = 2 * base[i][i] + base[i][j] - 2 * base[i][j] * base[i][j] / 255 - 255
      else:
        pixel = 2 * base[i][j] * base[i][j] / 255
      curr_row.append(pixel)
    output.append(curr_row)
  return output