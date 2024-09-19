from typing import List

from tenspiler.llm.python_dsl import (
    matrix_elemwise_div,
    matrix_scalar_sub,
    matrix_where,
)


def color_dodge_8_baseline(
    base: List[List[int]], active: List[List[int]]
) -> List[List[int]]:
    out = []
    m = len(base)
    n = len(base[0])

    for row in range(m):
        row_vec = []
        for col in range(n):
            if active[row][col] == 32:
                pixel = 32
            else:
                pixel = base[row][col] // (32 - active[row][col])
            row_vec.append(pixel)
        out.append(row_vec)

    return out


def color_dodge_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
    return matrix_where(
        active,
        matrix_elemwise_div(base, matrix_scalar_sub(32, active)),
        lambda a, b: 32 if a == 32 else b,
    )


active = [[123, 23, 46], [98, 98, 58]]
base = [[234, 87, 65], [10, 17, 70]]
print(color_dodge_8(base, active))
print(color_dodge_8_baseline(base, active))
