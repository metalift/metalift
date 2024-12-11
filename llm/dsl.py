from typing import Callable, List


def firsts(matrix: List[List[int]]) -> List[int]:
    return [] if len(matrix) < 1 else [matrix[0][0], *firsts(matrix[1:])]


def integer_exp(n: int) -> int:
    return 1 if n <= 0 else (integer_exp((n - 1)) * 3 % 64)


def integer_sqrt(n: int) -> int:
    return integer_sqrt_helper((n // 2), n)


def integer_sqrt_helper(n: int, guess: int) -> int:
    return (
        1
        if guess == 0 or guess == 1 or guess > 64
        else (
            guess
            if guess == (n // guess)
            else integer_sqrt_helper(n, (guess + (n // guess) // 2))
        )
    )


def ite_int(cond: bool, int_x: int, int_y: int) -> int:
    return int_x if cond else int_y


def matrix_col_slice(matrix: List[List[int]], start: int, end: int) -> List[List[int]]:
    return (
        []
        if len(matrix) < 1
        else [matrix[0][start:end], *matrix_col_slice(matrix[1:], start, end)]
    )


def matrix_elemwise_add(
    matrix_x: List[List[int]], matrix_y: List[List[int]]
) -> List[List[int]]:
    return (
        []
        if len(matrix_x) < 1 or not len(matrix_x) == len(matrix_y)
        else [
            vec_elemwise_add(matrix_x[0], matrix_y[0]),
            *matrix_elemwise_add(matrix_x[1:], matrix_y[1:]),
        ]
    )


def matrix_elemwise_div(
    matrix_x: List[List[int]], matrix_y: List[List[int]]
) -> List[List[int]]:
    return (
        []
        if len(matrix_x) < 1 or not len(matrix_x) == len(matrix_y)
        else [
            vec_elemwise_div(matrix_x[0], matrix_y[0]),
            *matrix_elemwise_div(matrix_x[1:], matrix_y[1:]),
        ]
    )


def matrix_elemwise_mul(
    matrix_x: List[List[int]], matrix_y: List[List[int]]
) -> List[List[int]]:
    return (
        []
        if len(matrix_x) < 1 or not len(matrix_x) == len(matrix_y)
        else [
            vec_elemwise_mul(matrix_x[0], matrix_y[0]),
            *matrix_elemwise_mul(matrix_x[1:], matrix_y[1:]),
        ]
    )


def matrix_elemwise_sub(
    matrix_x: List[List[int]], matrix_y: List[List[int]]
) -> List[List[int]]:
    return (
        []
        if len(matrix_x) < 1 or not len(matrix_x) == len(matrix_y)
        else [
            vec_elemwise_sub(matrix_x[0], matrix_y[0]),
            *matrix_elemwise_sub(matrix_x[1:], matrix_y[1:]),
        ]
    )


def matrix_row_slice(matrix: List[List[int]], start: int, end: int) -> List[List[int]]:
    return matrix[:end][start:]


def matrix_scalar_add(a: int, matrix_x: List[List[int]]) -> List[List[int]]:
    return (
        []
        if len(matrix_x) < 1
        else [vec_scalar_add(a, matrix_x[0]), *matrix_scalar_add(a, matrix_x[1:])]
    )


def matrix_scalar_div(a: int, matrix_x: List[List[int]]) -> List[List[int]]:
    return (
        []
        if len(matrix_x) < 1
        else [vec_scalar_div(a, matrix_x[0]), *matrix_scalar_div(a, matrix_x[1:])]
    )


def matrix_scalar_mul(a: int, matrix_x: List[List[int]]) -> List[List[int]]:
    return (
        []
        if len(matrix_x) < 1
        else [vec_scalar_mul(a, matrix_x[0]), *matrix_scalar_mul(a, matrix_x[1:])]
    )


def matrix_scalar_sub(a: int, matrix_x: List[List[int]]) -> List[List[int]]:
    return (
        []
        if len(matrix_x) < 1
        else [vec_scalar_sub(a, matrix_x[0]), *matrix_scalar_sub(a, matrix_x[1:])]
    )


def matrix_selection_two_args(
    matrix_x: List[List[int]],
    matrix_y: List[List[int]],
    select_two_args_arg: Callable[[int, int], int],
) -> List[List[int]]:
    return (
        []
        if len(matrix_x) < 1 or not len(matrix_x) == len(matrix_y)
        else [
            selection_two_args(matrix_x[0], matrix_y[0], select_two_args_arg),
            *matrix_selection_two_args(matrix_x[1:], matrix_y[1:], select_two_args_arg),
        ]
    )


def matrix_transpose(matrix: List[List[int]]) -> List[List[int]]:
    return [] if len(matrix) < 1 else [firsts(matrix), *matrix_transpose(rests(matrix))]


def matrix_vec_mul(matrix_x: List[List[int]], x: List[int]) -> List[int]:
    return (
        []
        if len(matrix_x) < 1 or len(matrix_x[0]) < 1 or not len(matrix_x[0]) == len(x)
        else [
            reduce_sum(vec_elemwise_mul(matrix_x[0], x)),
            *matrix_vec_mul(matrix_x[1:], x),
        ]
    )


def reduce_max(x: List[int]) -> int:
    return (
        (0 - 32)
        if len(x) < 1
        else (
            x[0]
            if len(x) == 1
            else (x[0] if x[0] > reduce_max(x[1:]) else reduce_max(x[1:]))
        )
    )


def reduce_mul(x: List[int]) -> int:
    return 1 if len(x) < 1 else x[0] * reduce_mul(x[1:])


def reduce_sum(x: List[int]) -> int:
    return 0 if len(x) < 1 else x[0] + reduce_sum(x[1:])


def rests(matrix: List[List[int]]) -> List[List[int]]:
    return [] if len(matrix) < 1 else matrix_col_slice(matrix, 1, len(matrix[0]))


def scalar_matrix_div(a: int, matrix_x: List[List[int]]) -> List[List[int]]:
    return (
        []
        if len(matrix_x) < 1
        else [scalar_vec_div(a, matrix_x[0]), *scalar_matrix_div(a, matrix_x[1:])]
    )


def scalar_matrix_sub(a: int, matrix_x: List[List[int]]) -> List[List[int]]:
    return (
        []
        if len(matrix_x) < 1
        else [scalar_vec_sub(a, matrix_x[0]), *scalar_matrix_sub(a, matrix_x[1:])]
    )


def scalar_vec_div(a: int, x: List[int]) -> List[int]:
    return [] if len(x) < 1 else [(a // x[0]), *scalar_vec_div(a, x[1:])]


def scalar_vec_sub(a: int, x: List[int]) -> List[int]:
    return [] if len(x) < 1 else [(a - x[0]), *scalar_vec_sub(a, x[1:])]


def selection_two_args(
    x: List[int], y: List[int], select_two_args_arg: Callable[[int, int], int]
) -> List[int]:
    return (
        []
        if len(x) < 1 or not len(x) == len(y)
        else [
            select_two_args_arg(x[0], y[0]),
            *selection_two_args(x[1:], y[1:], select_two_args_arg),
        ]
    )


def vec_elemwise_add(x: List[int], y: List[int]) -> List[int]:
    return (
        []
        if len(x) < 1 or not len(x) == len(y)
        else [x[0] + y[0], *vec_elemwise_add(x[1:], y[1:])]
    )


def vec_elemwise_div(x: List[int], y: List[int]) -> List[int]:
    return (
        []
        if len(x) < 1 or not len(x) == len(y)
        else [(x[0] // y[0]), *vec_elemwise_div(x[1:], y[1:])]
    )


def vec_elemwise_mul(x: List[int], y: List[int]) -> List[int]:
    return (
        []
        if len(x) < 1 or not len(x) == len(y)
        else [x[0] * y[0], *vec_elemwise_mul(x[1:], y[1:])]
    )


def vec_elemwise_sub(x: List[int], y: List[int]) -> List[int]:
    return (
        []
        if len(x) < 1 or not len(x) == len(y)
        else [(x[0] - y[0]), *vec_elemwise_sub(x[1:], y[1:])]
    )


def vec_map(x: List[int], map_int_to_int: Callable[[int], int]) -> List[int]:
    return [] if len(x) < 1 else [map_int_to_int(x[0]), *vec_map(x[1:], map_int_to_int)]


def vec_scalar_add(a: int, x: List[int]) -> List[int]:
    return [] if len(x) < 1 else [a + x[0], *vec_scalar_add(a, x[1:])]


def vec_scalar_div(a: int, x: List[int]) -> List[int]:
    return [] if len(x) < 1 else [(x[0] // a), *vec_scalar_div(a, x[1:])]


def vec_scalar_mul(a: int, x: List[int]) -> List[int]:
    return [] if len(x) < 1 else [a * x[0], *vec_scalar_mul(a, x[1:])]


def vec_scalar_sub(a: int, x: List[int]) -> List[int]:
    return [] if len(x) < 1 else [(x[0] - a), *vec_scalar_sub(a, x[1:])]


def vec_slice(lst: List[int], start: int, end: int) -> List[int]:
    return lst[:end][start:]
