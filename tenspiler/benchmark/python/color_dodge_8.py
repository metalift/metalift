from typing import List


def color_dodge_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
    output: List[List[int]] = []
    m = len(base)
    n = len(base[0])
    for i in range(m):
        curr_row: List[int] = []
        for j in range(n):
            if active[i][j] == 255:
                pixel = 255
            else:
                pixel = base[i][j] / (255 - active[i][j])
            curr_row.append(pixel)
        output.append(curr_row)
    return output
