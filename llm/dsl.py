from typing import List


def vec_elemwise_mul(x: List[int], y: List[int]) -> List[int]:
    return [] if len(x) < 1 else [x[0] * y[0], *vec_elemwise_mul(x[1:], y[1:])]


def vec_scalar_mul(a: int, x: List[int]) -> List[int]:
    return [] if len(x) < 1 else [a * x[0], *vec_scalar_mul(a, x[1:])]


def integer_sqrt(x: int) -> int:
    return x
