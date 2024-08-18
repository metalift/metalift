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


def transformer_part2(
    token_position: int,
    head: int,
    head_size: int,
    key_cache_layer: list[list[int]],
    attention: list[int],
) -> list[int]:
    xb: list[int] = []
    for i in range(head_size):
        curr = 0
        for timestep in range(token_position + 1):
            curr += (
                attention[timestep] * key_cache_layer[timestep][head * head_size + i]
            )
        xb.append(curr)
    return xb


if __name__ == "__main__":
    inputs = [
        {
            "token_position": 1,
            "head": 0,
            "head_size": 1,
            "key_cache_layer": [[1, 2], [3, 4]],
            "attention": [2, 3],
        },
        {
            "token_position": 2,
            "head": 1,
            "head_size": 2,
            "key_cache_layer": [[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12]],
            "attention": [3, 2, 1],
        },
        {
            "token_position": 3,
            "head": 0,
            "head_size": 3,
            "key_cache_layer": [
                [1, 2, 3, 4, 5],
                [6, 7, 8, 9, 10],
                [11, 12, 13, 14, 15],
                [16, 17, 18, 19, 20],
            ],
            "attention": [4, 3, 2, 1],
        },
        {
            "token_position": 1,
            "head": 2,
            "head_size": 1,
            "key_cache_layer": [[1, 2, 3], [4, 5, 6], [7, 8, 9]],
            "attention": [1, 3, 2],
        },
        {
            "token_position": 2,
            "head": 1,
            "head_size": 2,
            "key_cache_layer": [[2, 4, 6, 8], [10, 12, 14, 16], [18, 20, 22, 24]],
            "attention": [1, 1, 1],
        },
    ]

    # inputs = [
    #     {
    #         "token_position": 1,
    #         "head": 0,
    #         "head_size": 1,
    #         "key_cache_layer": [[1, 2], [3, 4]],
    #         "q": [1, 2]
    #     },
    #     {
    #         "token_position": 2,
    #         "head": 1,
    #         "head_size": 1,
    #         "key_cache_layer": [[1, 2, 3], [4, 5, 6], [7, 8, 9]],
    #         "q": [1, 2, 3],
    #     },
    #     {
    #         "token_position": 3,
    #         "head": 0,
    #         "head_size": 2,
    #         "key_cache_layer": [[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12], [13, 14, 15, 16]],
    #         "q": [1, 2, 3, 4],
    #     },
    #     {
    #         "token_position": 2,
    #         "head": 0,
    #         "head_size": 2,
    #         "key_cache_layer": [[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12]],
    #         "q": [4, 3, 2, 1],
    #     },
    #     {
    #         "token_position": 3,
    #         "head": 1,
    #         "head_size": 2,
    #         "key_cache_layer": [[10, 20, 30, 40, 50], [60, 70, 80, 90, 100], [110, 120, 130, 140, 150], [160, 170, 180, 190, 200]],
    #         "q": [5, 4, 3, 2, 1],
    #     }
    # ]
    for input in inputs:
        print(transformer_part2(**input))
    # inputs = [
    #     {
    #         "base": [[30, 20], [10, 5]],
    #         "active": [[2, 4], [8, 10]]
    #     },
    #     {
    #         "base": [[0, 32], [16, 24]],
    #         "active": [[1, 1], [1, 1]]
    #     },
    #     {
    #         "base": [[32, 32], [32, 32]],
    #         "active": [[0, 0], [0, 0]]
    #     },
    #     {
    #         "base": [[10, 0], [15, 32]],
    #         "active": [[2, 3], [5, 8]]
    #     },
    #     {
    #         "base": [[31, 1], [2, 30]],
    #         "active": [[5, 7], [9, 11]]
    #     },
    #     {
    #         "base": [[16, 8], [24, 32]],
    #         "active": [[16, 8], [4, 2]]
    #     },
    #     {
    #         "base": [[5, 10], [15, 20]],
    #         "active": [[0, 1], [2, 4]]
    #     },
    #     {
    #         "base": [[10, 20], [30, 40]],
    #         "active": [[32, 16], [8, 4]]
    #     }
    # ]

    # for input in inputs:
    #     print(color_burn_8(input["base"], input["active"]))
