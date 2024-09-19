from typing import List

from tenspiler.llm.python_dsl import (
    matrix_col_slice,
    matrix_elemwise_sub,
    matrix_row_slice,
    matrix_scalar_mul,
)


def fdtd_2d_part1_original(
    nx: int, ny: int, ey: List[List[int]], hz: List[List[int]]
) -> List[List[int]]:
    out = []
    for i in range(1, nx):
        row_vec = []
        for j in range(ny):
            curr = ey[i][j] - 5 * (hz[i][j] - hz[i - 1][j])
            row_vec.append(curr)
        out.append(row_vec)
    return out


def fdtd_2d_part1(
    nx: int, ny: int, ey: List[List[int]], hz: List[List[int]]
) -> List[List[int]]:
    return matrix_elemwise_sub(
        matrix_row_slice(ey, 1, nx),
        matrix_scalar_mul(
            5,
            matrix_elemwise_sub(
                matrix_row_slice(hz, 1, nx), matrix_row_slice(hz, 0, nx - 1)
            ),
        ),
    )


def fdtd_2d_part1_fixed(
    nx: int, ny: int, ey: List[List[int]], hz: List[List[int]]
) -> List[List[int]]:
    return matrix_col_slice(
        matrix_elemwise_sub(
            matrix_row_slice(ey, 1, nx),
            matrix_scalar_mul(
                5,
                matrix_elemwise_sub(
                    matrix_row_slice(hz, 1, nx), matrix_row_slice(hz, 0, nx - 1)
                ),
            ),
        ),
        0,
        ny,
    )


nx = 4
ny = 3
ey = [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
hz = [[10, 11, 12], [13, 14, 15], [16, 17, 18]]
print(fdtd_2d_part1(nx, ny, ey, hz))
print(fdtd_2d_part1_original(nx, ny, ey, hz))
print(fdtd_2d_part1_fixed(nx, ny, ey, hz))
