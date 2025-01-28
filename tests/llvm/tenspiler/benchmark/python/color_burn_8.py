from typing import List


def color_burn_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
    output: List[List[int]] = []
    m = len(base)
    n = len(base[0])
    for i in range(m):
        curr_row: List[int] = []
        for j in range(n):
            if active[i][j] == 0:
                pixel = 255
            else:
                pixel = 255 - (255 - base[i][j]) / active[i][j]
            curr_row.append(pixel)
        output.append(curr_row)
    return output
