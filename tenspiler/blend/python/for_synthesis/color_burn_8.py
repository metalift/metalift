from tenspiler.llm.python_dsl import matrix_scalar_div, matrix_scalar_sub, matrix_where


def color_burn_8(base: list[list[int]], active: list[list[int]]) -> list[list[int]]:
    return matrix_where(
        active,
        matrix_scalar_sub(32, matrix_scalar_div(32, active)),
        lambda a, b: 32 if a == 0 else (32 - (32 - b) // a),
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


active = [[1, 2, 3], [4, 5, 6]]
base = [[7, 8, 9], [10, 11, 12]]
print(color_burn_8(base, active))
print(color_burn_8_baseline(base, active))


[[-32, 0, 11], [16, 20, 22]]
