from typing import Callable, List


def vec_elemwise_mul(x: List[int], y: List[int]) -> List[int]:
    return (
        []
        if len(x) < 1 or not len(x) == len(y)
        else [x[0] * y[0], *vec_elemwise_mul(x[1:], y[1:])]
    )


def vec_scalar_mul(a: int, x: List[int]) -> List[int]:
    return [] if len(x) < 1 else [a * x[0], *vec_scalar_mul(a, x[1:])]


def reduce_sum(x: List[int]) -> int:
    return 0 if len(x) < 1 else x[0] + reduce_sum(x[1:])


def integer_sqrt(n: int) -> int:
    return integer_sqrt_helper((n // 2), n)


def vec_map(x: List[int], map_int_to_int: Callable[[int], int]) -> List[int]:
    return [] if len(x) < 1 else [map_int_to_int(x[0]), *vec_map(x[1:], map_int_to_int)]
