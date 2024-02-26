import math


def reduce_max(x):
    return x[0] if len(x) <= 1 else (x[0] if x[0] > max(x[1:]) else max(x[1:]))


def reduce_sum(x):
    return 0 if len(x) < 1 else x[0] + sum(x[1:])


def reduce_mul(x):
    return 1 if len(x) < 1 else x[0] * math.prod(x[1:])


def matrix_vec_mul(matrix_x, x):
    return (
        []
        if len(matrix_x) < 1 or len(matrix_x[0]) < 1 or not len(matrix_x[0]) == len(x)
        else [sum(vec_elemwise_mul(matrix_x[0], x)), *matrix_vec_mul(matrix_x[1:], x)]
    )


def vec_elemwise_mul(x, y):
    return (
        []
        if len(x) < 1 or not len(x) == len(y)
        else [x[0] * y[0], *vec_elemwise_mul(x[1:], y[1:])]
    )


def reduce_sum(x):
    return 0 if len(x) < 1 else x[0] + sum(x[1:])


def vec_elemwise_add(x, y):
    return (
        []
        if len(x) < 1 or not len(x) == len(y)
        else [x[0] + y[0], *vec_elemwise_add(x[1:], y[1:])]
    )


def vec_elemwise_sub(x, y):
    return (
        []
        if len(x) < 1 or not len(x) == len(y)
        else [x[0] - y[0], *vec_elemwise_sub(x[1:], y[1:])]
    )


def vec_elemwise_mul(x, y):
    return (
        []
        if len(x) < 1 or not len(x) == len(y)
        else [x[0] * y[0], *vec_elemwise_mul(x[1:], y[1:])]
    )


def vec_elemwise_div(x, y):
    return (
        []
        if len(x) < 1 or not len(x) == len(y)
        else [x[0] // y[0], *vec_elemwise_div(x[1:], y[1:])]
    )


def matrix_elemwise_add(matrix_x, matrix_y):
    return (
        []
        if len(matrix_x) < 1 or not len(matrix_x) == len(matrix_y)
        else [
            vec_elemwise_add(matrix_x[0], matrix_y[0]),
            *matrix_elemwise_add(matrix_x[1:], matrix_y[1:]),
        ]
    )


def matrix_elemwise_sub(matrix_x, matrix_y):
    return (
        []
        if len(matrix_x) < 1 or not len(matrix_x) == len(matrix_y)
        else [
            vec_elemwise_sub(matrix_x[0], matrix_y[0]),
            *matrix_elemwise_sub(matrix_x[1:], matrix_y[1:]),
        ]
    )


def matrix_elemwise_mul(matrix_x, matrix_y):
    return (
        []
        if len(matrix_x) < 1 or not len(matrix_x) == len(matrix_y)
        else [
            vec_elemwise_mul(matrix_x[0], matrix_y[0]),
            *matrix_elemwise_mul(matrix_x[1:], matrix_y[1:]),
        ]
    )


def matrix_elemwise_div(matrix_x, matrix_y):
    return (
        []
        if len(matrix_x) < 1 or not len(matrix_x) == len(matrix_y)
        else [
            vec_elemwise_div(matrix_x[0], matrix_y[0]),
            *matrix_elemwise_div(matrix_x[1:], matrix_y[1:]),
        ]
    )


def vec_scalar_add(a, x):
    return [] if len(x) < 1 else [a + x[0], *vec_scalar_add(a, x[1:])]


def vec_scalar_sub(a, x):
    return [] if len(x) < 1 else [x[0] - a, *vec_scalar_sub(a, x[1:])]


def vec_scalar_mul(a, x):
    return [] if len(x) < 1 else [a * x[0], *vec_scalar_mul(a, x[1:])]


def vec_scalar_div(a, x):
    return [] if len(x) < 1 else [x[0] // a, *vec_scalar_div(a, x[1:])]


def scalar_vec_sub(a, x):
    return [] if len(x) < 1 else [a - x[0], *scalar_vec_sub(a, x[1:])]


def scalar_vec_div(a, x):
    return [] if len(x) < 1 else [a // x[0], *scalar_vec_div(a, x[1:])]


def matrix_scalar_add(a, matrix_x):
    return (
        []
        if len(matrix_x) < 1
        else [vec_scalar_add(a, matrix_x[0]), *matrix_scalar_add(a, matrix_x[1:])]
    )


def matrix_scalar_sub(a, matrix_x):
    return (
        []
        if len(matrix_x) < 1
        else [vec_scalar_sub(a, matrix_x[0]), *matrix_scalar_sub(a, matrix_x[1:])]
    )


def matrix_scalar_mul(a, matrix_x):
    return (
        []
        if len(matrix_x) < 1
        else [vec_scalar_mul(a, matrix_x[0]), *matrix_scalar_mul(a, matrix_x[1:])]
    )


def matrix_scalar_div(a, matrix_x):
    return (
        []
        if len(matrix_x) < 1
        else [vec_scalar_div(a, matrix_x[0]), *matrix_scalar_div(a, matrix_x[1:])]
    )


def scalar_matrix_sub(a, matrix_x):
    return (
        []
        if len(matrix_x) < 1
        else [scalar_vec_sub(a, matrix_x[0]), *scalar_matrix_sub(a, matrix_x[1:])]
    )


def scalar_matrix_div(a, matrix_x):
    return (
        []
        if len(matrix_x) < 1
        else [scalar_vec_div(a, matrix_x[0]), *scalar_matrix_div(a, matrix_x[1:])]
    )


def vec_map(x, map_int_to_int):
    return [] if len(x) < 1 else [map_int_to_int(x[0]), *vec_map(x[1:], map_int_to_int)]


def matrix_selection_two_args(matrix_x, matrix_y, select_two_args_arg):
    return (
        []
        if len(matrix_x) < 1 or not len(matrix_x) == len(matrix_y)
        else [
            selection_two_args(matrix_x[0], matrix_y[0], select_two_args_arg),
            *matrix_selection_two_args(matrix_x[1:], matrix_y[1:], select_two_args_arg),
        ]
    )


def selection_two_args(x, y, select_two_args_arg):
    return (
        []
        if len(x) < 1 or not len(x) == len(y)
        else [
            select_two_args_arg(x[0], y[0]),
            *selection_two_args(x[1:], y[1:], select_two_args_arg),
        ]
    )


if __name__ == "__main__":
    x = [1, 2, 3]
    y = [4, 5, 6]
    matrix_x = [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
    scalar = 4
    print("reduce_max", reduce_max(x))
    print("reduce_sum", reduce_sum(x))
    print("reduce_mul", reduce_mul(x))
    print("matrix_vec_mul", matrix_vec_mul(matrix_x, x))
    print("vec_elemwise_add", vec_elemwise_add(x, y))
    print("vec_elemwise_sub", vec_elemwise_sub(x, y))
    print("vec_elemwise_mul", vec_elemwise_mul(x, y))
    print("vec_elemwise_div", vec_elemwise_div(x, y))
    print("matrix_elemwise_add", matrix_elemwise_add(matrix_x, matrix_x))
    print("matrix_elemwise_sub", matrix_elemwise_sub(matrix_x, matrix_x))
    print("matrix_elemwise_mul", matrix_elemwise_mul(matrix_x, matrix_x))
    print("matrix_elemwise_div", matrix_elemwise_div(matrix_x, matrix_x))
    print("vec_scalar_add", vec_scalar_add(scalar, x))
    print("vec_scalar_sub", vec_scalar_sub(scalar, x))
    print("vec_scalar_mul", vec_scalar_mul(scalar, x))
    print("vec_scalar_div", vec_scalar_div(scalar, x))
    print("scalar_vec_sub", scalar_vec_sub(scalar, x))
    print("scalar_vec_div", scalar_vec_div(scalar, x))
    print("matrix_scalar_add", matrix_scalar_add(scalar, matrix_x))
    print("matrix_scalar_sub", matrix_scalar_sub(scalar, matrix_x))
    print("matrix_scalar_mul", matrix_scalar_mul(scalar, matrix_x))
    print("matrix_scalar_div", matrix_scalar_div(scalar, matrix_x))
    print("scalar_matrix_sub", scalar_matrix_sub(scalar, matrix_x))
    print("scalar_matrix_div", scalar_matrix_div(scalar, matrix_x))
    print("vec_map", vec_map(x, lambda x: x + 1))
    print(
        "matrix_selection_two_args",
        matrix_selection_two_args(matrix_x, matrix_x, lambda x, y: x + y),
    )
