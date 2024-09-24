from typing import List

from tenspiler.llm.python_dsl import (
    matrix_elemwise_div,
    matrix_scalar_sub,
    matrix_where,
    scalar_matrix_div,
    scalar_matrix_sub,
)


def color_burn_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
    return matrix_where(
        active,
        matrix_scalar_sub(32, matrix_elemwise_div(scalar_matrix_sub(32, base), active)),
        lambda a, b: 32 if a == 0 else b,
    )


def color_burn_8_baseline(
    base: list[list[int]], active: list[list[int]]
) -> list[list[int]]:
    result = []
    for i in range(len(base)):
        row = []
        for j in range(len(base[0])):
            if active[i][j] == 0:
                row.append(32)
            else:
                row.append(32 - (32 - base[i][j]) // active[i][j])
        result.append(row)
    return result


# active = [[1, 2, 3], [4, 5, 6]]
# base = [[7, 8, 9], [10, 11, 12]]
# # print(color_burn_8(base, active))
# print(color_burn_8_baseline(base, active))

# def color_burn_8(base, active):
#     return matrix_where(
#         active,
#         matrix_scalar_sub(32, matrix_elemwise_div(matrix_scalar_sub(32, base), active)),
#         lambda a, b: 32 if a == 0 else b
#     )


def color_burn_8_sol1(
    base: List[List[int]], active: List[List[int]]
) -> List[List[int]]:
    return matrix_where(
        active,
        matrix_scalar_sub(32, matrix_elemwise_div(matrix_scalar_sub(32, base), active)),
        lambda a, b: 32 if a == 0 else b,
    )


def color_burn_8_sol2(
    base: List[List[int]], active: List[List[int]]
) -> List[List[int]]:
    return matrix_where(
        active,
        matrix_scalar_sub(32, scalar_matrix_div(32, matrix_scalar_sub(32, base))),
        lambda a, b: 32 if a == 0 else b,
    )


def color_burn_8_sol3(
    base: List[List[int]], active: List[List[int]]
) -> List[List[int]]:
    return matrix_where(
        active,
        matrix_scalar_sub(32, matrix_elemwise_div(scalar_matrix_sub(32, base), active)),
        lambda a, b: 32 if a == 0 else b,
    )


def color_burn_8_correct_translation(base, active):
    return matrix_where(
        active,
        scalar_matrix_sub(32, matrix_elemwise_div(scalar_matrix_sub(32, base), active)),
        lambda a, b: 32 if a == 0 else b,
    )


base = active = [[1, 2], [3, 4]]
print(color_burn_8_sol1(base, active))
print(color_burn_8_sol2(base, active))
print(color_burn_8_sol3(base, active))
print(color_burn_8_correct_translation(base, active))
