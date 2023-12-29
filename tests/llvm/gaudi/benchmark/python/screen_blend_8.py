from typing import List

def screen_blend_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
  output: List[List[int]] = []
  m = len(base)
  n = len(base[0])
  for i in range(m):
    curr_row: List[int] = []
    for j in range(n):
      pixel = base[i][j] + active[i][j] - (base[i][j] * active[i][j]) / 255
      curr_row.append(pixel)
    output.append(curr_row)
  return output