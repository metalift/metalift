from typing import List


def depthwise_conv_1d(
    matrix_x: List[List[int]], matrix_y: List[List[int]]
) -> List[List[int]]:
    return (
        []
        if len(matrix_x) < 1
        else [
            conv_1d(matrix_x[0], matrix_y[0]),
            *depthwise_conv_1d(matrix_x[1:], matrix_y[1:]),
        ]
    )


def conv_1d(x: List[int], f: List[int]) -> List[int]:
    return (
        []
        if len(x) < 1
        else [(0 if len(x) < len(f) else dot(x[: len(f)], f)), *conv_1d(x[1:], f)]
    )


def dot(x: List[int], f: List[int]) -> int:
    return 0 if len(f) < 1 else x[0] * f[0] + dot(x[1:], f[1:])
