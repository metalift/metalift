from typing import List


def conv1d(x: List[int], y: List[int], W: int, W_f: int) -> int:
    return (
        []
        if W < 1
        else [reduce_sum(vec_elemwise_mul(x[:W_f], y)), *conv1d(x[1:], y, (W - 1), W_f)]
    )


def vec_elemwise_mul(x: List[int], y: List[int]) -> List[int]:
    return (
        []
        if len(x) < 1 or not len(x) == len(y)
        else [x[0] * y[0], *vec_elemwise_mul(x[1:], y[1:])]
    )


def reduce_sum(x: List[int]) -> int:
    return 0 if len(x) < 1 else x[0] + reduce_sum(x[1:])
