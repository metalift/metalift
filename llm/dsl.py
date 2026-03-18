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
    return [] if len(x) < len(f) else [dot(x[: len(f)], f), *conv_1d(x[len(f) :], f)]


def dot(x: List[int], f: List[int]) -> int:
    return 0 if len(f) < 1 else x[0] * f[0] + dot(x[1:], f[1:])


def vec_elemwise_mul(x: List[int], y: List[int]) -> List[int]:
    return (
        []
        if len(x) < 1 or not len(x) == len(y)
        else [x[0] * y[0], *vec_elemwise_mul(x[1:], y[1:])]
    )


def reduce_sum(x: List[int]) -> int:
    return 0 if len(x) < 1 else x[0] + reduce_sum(x[1:])
