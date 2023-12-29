from numba import njit

@njit
def linear_dodge_8(base, active):
  output = []
  m = len(base)
  n = len(base[0])
  for i in range(m):
    curr_row = []
    for j in range(n):
      pixel = base[i][j] + active[i][j]
      curr_row.append(pixel)
    output.append(curr_row)
  return output