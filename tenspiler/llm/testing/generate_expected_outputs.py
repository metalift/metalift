# def integer_sqrt(n: int) -> int:
#     return n

# def transformer_part1(
#     token_position: int,
#     head: int,
#     head_size: int,
#     key_cache_layer: list[list[int]],
#     q: list[int]
# ) -> list[int]:
#     attention: list[int] = []
#     # key_cache_layer = matrix_scalar_div(head_size, key_cache_layer)
#     for timestep in range(token_position):
#         score: int = 0
#         for i in range(head_size):
#             score += q[head * head_size + i] * key_cache_layer[timestep][head * head_size + i]
#         score //= integer_sqrt(head_size * 1)
#         attention.append(score)
#     return attention

# def lighten_blend_8(base: list[list[int]], active: list[list[int]]) -> list[list[int]]:
#     result: list[list[int]] = []
#     for i in range(len(base)):
#         row: list[int] = []
#         for j in range(len(base[i])):
#             if base[i][j] < active[i][j]:
#                 row.append(active[i][j])
#             else:
#                 row.append(base[i][j])
#         result.append(row)
#     return result

# def color_burn_8(base: list[list[int]], active: list[list[int]]) -> list[list[int]]:
#     result: list[list[int]] = []
#     for i in range(len(base)):
#         row: list[int] = []
#         for j in range(len(base[i])):
#             pixel: int
#             if active[i][j] == 0:
#                 pixel = 32
#             else:
#                 pixel = 32 - (32 - base[i][j]) // active[i][j]
#             row.append(pixel)
#         result.append(row)
#     return result


# def transformer_part2(
#     token_position: int,
#     head: int,
#     head_size: int,
#     key_cache_layer: list[list[int]],
#     attention: list[int],
# ) -> list[int]:
#     xb: list[int] = []
#     for i in range(head_size):
#         curr = 0
#         for timestep in range(token_position + 1):
#             curr += (
#                 attention[timestep] * key_cache_layer[timestep][head * head_size + i]
#             )
#         xb.append(curr)
#     return xb


def fdtd_2d_part2(
    nx: int, ny: int, ex: list[list[int]], hz: list[list[int]]
) -> list[list[int]]:
    out: list[list[int]] = []
    for i in range(nx):
        row_vec = []
        for j in range(1, ny):
            curr = ex[i][j] - 5 * (hz[i][j] - hz[i][j - 1])
            row_vec.append(curr)
        out.append(row_vec)
    return out


if __name__ == "__main__":
    inputs = [
        {"nx": 2, "ny": 3, "ex": [[1, 2, 3], [4, 5, 6]], "hz": [[1, 1, 1], [0, 1, 0]]},
        {
            "nx": 3,
            "ny": 4,
            "ex": [[0, 0, 0, 0], [1, 1, 1, 1], [2, 2, 2, 2]],
            "hz": [[1, 2, 3, 4], [4, 3, 2, 1], [0, 0, 0, 0]],
        },
        {"nx": 1, "ny": 2, "ex": [[5, 6]], "hz": [[1, 2]]},
        {
            "nx": 2,
            "ny": 3,
            "ex": [[7, 8, 9], [10, 11, 12]],
            "hz": [[1, 2, 3], [3, 2, 1]],
        },
        {"nx": 2, "ny": 2, "ex": [[3, 4], [5, 6]], "hz": [[2, 3], [1, 1]]},
    ]
    for input in inputs:
        print(fdtd_2d_part2(**input))
