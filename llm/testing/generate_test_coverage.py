# from test import lighten_blend_8
# from test import color_burn_8
# from test import transformer_part1
# from test import transformer_part2
import pytest

from llm.testing.generate_expected_outputs import fdtd_2d_part2


@pytest.mark.parametrize(
    "inputs, expected",
    [
        (
            {
                "nx": 2,
                "ny": 3,
                "ex": [[1, 2, 3], [4, 5, 6]],
                "hz": [[1, 1, 1], [0, 1, 0]],
            },
            [[2, 3], [0, 11]],
        ),
        (
            {
                "nx": 3,
                "ny": 4,
                "ex": [[0, 0, 0, 0], [1, 1, 1, 1], [2, 2, 2, 2]],
                "hz": [[1, 2, 3, 4], [4, 3, 2, 1], [0, 0, 0, 0]],
            },
            [[-5, -5, -5], [6, 6, 6], [2, 2, 2]],
        ),
        ({"nx": 1, "ny": 2, "ex": [[5, 6]], "hz": [[1, 2]]}, [[1]]),
        (
            {
                "nx": 2,
                "ny": 3,
                "ex": [[7, 8, 9], [10, 11, 12]],
                "hz": [[1, 2, 3], [3, 2, 1]],
            },
            [[3, 4], [16, 17]],
        ),
        (
            {"nx": 2, "ny": 2, "ex": [[3, 4], [5, 6]], "hz": [[2, 3], [1, 1]]},
            [[-1], [6]],
        ),
    ],
)
def test_fdtd_2d_part2(inputs, expected):
    assert fdtd_2d_part2(**inputs) == expected


# @pytest.mark.parametrize(
#     "token_position, head, head_size, key_cache_layer, attention, expected",
#     [
#         (1, 0, 1, [[1, 2], [3, 4]], [2, 3], [11]),
#         (2, 1, 2, [[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12]], [3, 2, 1], [34, 40]),
#         (
#             3,
#             0,
#             3,
#             [
#                 [1, 2, 3, 4, 5],
#                 [6, 7, 8, 9, 10],
#                 [11, 12, 13, 14, 15],
#                 [16, 17, 18, 19, 20],
#             ],
#             [4, 3, 2, 1],
#             [60, 70, 80],
#         ),
#         (1, 2, 1, [[1, 2, 3], [4, 5, 6], [7, 8, 9]], [1, 3, 2], [21]),
#         (
#             2,
#             1,
#             2,
#             [[2, 4, 6, 8], [10, 12, 14, 16], [18, 20, 22, 24]],
#             [1, 1, 1],
#             [42, 48],
#         ),
#     ],
# )
# def test_transformer_part2(
#     token_position, head, head_size, key_cache_layer, attention, expected
# ):
#     result = transformer_part2(
#         token_position, head, head_size, key_cache_layer, attention
#     )
#     assert result == expected


# @pytest.mark.parametrize(
#     "base, active, expected",
#     [
#         ([[30, 20], [10, 5]], [[2, 4], [8, 10]], [[31, 29], [30, 30]]),
#         ([[0, 32], [16, 24]], [[1, 1], [1, 1]], [[0, 32], [16, 24]]),
#         ([[32, 32], [32, 32]], [[0, 0], [0, 0]], [[32, 32], [32, 32]]),
#         ([[10, 0], [15, 32]], [[2, 3], [5, 8]], [[21, 22], [29, 32]]),
#         ([[31, 1], [2, 30]], [[5, 7], [9, 11]], [[32, 28], [29, 32]]),
#         ([[16, 8], [24, 32]], [[16, 8], [4, 2]], [[31, 29], [30, 32]]),
#         ([[5, 10], [15, 20]], [[0, 1], [2, 4]], [[32, 10], [24, 29]]),
#         ([[10, 20], [30, 40]], [[32, 16], [8, 4]], [[32, 32], [32, 34]])
#     ]
# )
# def test_color_burn_8(base, active, expected):
#     assert color_burn_8(base, active) == expected

# @pytest.mark.parametrize("base, active, expected", [
#     (
#         [[10, 50, 90], [200, 150, 100], [255, 255, 255]],
#         [[20, 40, 100], [190, 160, 110], [255, 250, 245]],
#         [[20, 50, 100], [200, 160, 110], [255, 255, 255]]
#     ),
#     (
#         [[255, 0, 128], [64, 128, 192], [100, 150, 200]],
#         [[0, 255, 127], [63, 129, 193], [99, 151, 199]],
#         [[255, 255, 128], [64, 129, 193], [100, 151, 200]]
#     ),
#     (
#         [[0, 0, 0], [0, 0, 0], [0, 0, 0]],
#         [[255, 255, 255], [255, 255, 255], [255, 255, 255]],
#         [[255, 255, 255], [255, 255, 255], [255, 255, 255]]
#     )
# ])
# def test_lighten_blend_8(base, active, expected):
#     assert lighten_blend_8(base, active) == expected

# @pytest.mark.parametrize("token_position, head, head_size, key_cache_layer, q, expected", [
#     (
#         1,
#         0,
#         1,
#         [[1, 2], [3, 4]],
#         [1, 2],
#         [1]
#     ),
#     (
#         2,
#         1,
#         1,
#         [[1, 2, 3], [4, 5, 6], [7, 8, 9]],
#         [1, 2, 3],
#         [4, 10]
#     ),
#     (
#         3,
#         0,
#         2,
#         [[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12], [13, 14, 15, 16]],
#         [1, 2, 3, 4],
#         [2, 8, 14]
#     ),
#     (
#         2,
#         0,
#         2,
#         [[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12]],
#         [4, 3, 2, 1],
#         [5, 19]
#     ),
#     (
#         3,
#         1,
#         2,
#         [[10, 20, 30, 40, 50], [60, 70, 80, 90, 100], [110, 120, 130, 140, 150], [160, 170, 180, 190, 200]],
#         [5, 4, 3, 2, 1],
#         [85, 210, 335]
#     )
# ])
# def test_transformer_part1(token_position, head, head_size, key_cache_layer, q, expected):
#     assert transformer_part1(token_position, head, head_size, key_cache_layer, q) == expected
