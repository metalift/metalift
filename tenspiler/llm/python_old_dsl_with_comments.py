from typing import Any, Callable, List


def ite(cond: bool, if_then: Any, if_else: Any) -> Any:
    # Return if_then if cond else if_else
    return if_then if cond else if_else


def reduce_sum(x: List[int]) -> int:
    # Sum all elements in a vector.
    return 0 if len(x) < 1 else x[0] + reduce_sum(x[1:])


def vec_elemwise_mul(x: List[int], y: List[int]) -> List[int]:
    # Element-wise multiplication of two vectors.
    return (
        []
        if len(x) < 1 or not len(x) == len(y)
        else [x[0] * y[0], *vec_elemwise_mul(x[1:], y[1:])]
    )


def reduce_max(x: List[int]) -> int:
    # Return the maximum element in a vector.
    return (
        x[0]
        if len(x) <= 1
        else (x[0] if x[0] > reduce_max(x[1:]) else reduce_max(x[1:]))
    )


def vec_elemwise_add(x: List[int], y: List[int]) -> List[int]:
    # Element-wise addition of two vectors.
    return (
        []
        if len(x) < 1 or not len(x) == len(y)
        else [x[0] + y[0], *vec_elemwise_add(x[1:], y[1:])]
    )


def vec_elemwise_sub(x: List[int], y: List[int]) -> List[int]:
    # Element-wise subtraction of two vectors.
    return (
        []
        if len(x) < 1 or not len(x) == len(y)
        else [x[0] - y[0], *vec_elemwise_sub(x[1:], y[1:])]
    )


def vec_elemwise_div(x: List[int], y: List[int]) -> List[int]:
    # Element-wise division of two vectors.
    return (
        []
        if len(x) < 1 or not len(x) == len(y)
        else [x[0] // y[0], *vec_elemwise_div(x[1:], y[1:])]
    )


def matrix_elemwise_add(
    matrix_x: List[List[int]], matrix_y: List[List[int]]
) -> List[List[int]]:
    # Element-wise addition of two matrices.
    return (
        []
        if len(matrix_x) < 1 or not len(matrix_x) == len(matrix_y)
        else [
            vec_elemwise_add(matrix_x[0], matrix_y[0]),
            *matrix_elemwise_add(matrix_x[1:], matrix_y[1:]),
        ]
    )


def matrix_elemwise_sub(
    matrix_x: List[List[int]], matrix_y: List[List[int]]
) -> List[List[int]]:
    # Element-wise subtraction of two matrices.
    return (
        []
        if len(matrix_x) < 1 or not len(matrix_x) == len(matrix_y)
        else [
            vec_elemwise_sub(matrix_x[0], matrix_y[0]),
            *matrix_elemwise_sub(matrix_x[1:], matrix_y[1:]),
        ]
    )


def matrix_scalar_sub(a: int, matrix_x: List[List[int]]) -> List[List[int]]:
    # Subtract a scalar 'a' from each element of the matrix.
    # matrix_x[i][j] = matrix_x[i][j] - a
    return (
        []
        if len(matrix_x) < 1
        else [vec_scalar_sub(a, matrix_x[0]), *matrix_scalar_sub(a, matrix_x[1:])]
    )


def matrix_scalar_mul(a: int, matrix_x: List[List[int]]) -> List[List[int]]:
    # Multiply a scalar 'a' with each element of the matrix.
    # matrix_x[i][j] = matrix_x[i][j] * a
    return (
        []
        if len(matrix_x) < 1
        else [vec_scalar_mul(a, matrix_x[0]), *matrix_scalar_mul(a, matrix_x[1:])]
    )


def matrix_transpose(matrix: List[List[int]]) -> List[List[int]]:
    # Transpose a matrix.
    return [] if len(matrix) < 1 else [firsts(matrix), *matrix_transpose(rests(matrix))]


def matrix_elemwise_div(
    matrix_x: List[List[int]], matrix_y: List[List[int]]
) -> List[List[int]]:
    # Element-wise division of two matrices.
    return (
        []
        if len(matrix_x) < 1 or not len(matrix_x) == len(matrix_y)
        else [
            vec_elemwise_div(matrix_x[0], matrix_y[0]),
            *matrix_elemwise_div(matrix_x[1:], matrix_y[1:]),
        ]
    )


def vec_scalar_add(a: int, x: List[int]) -> List[int]:
    # Add a scalar to each element in a vector.
    return [] if len(x) < 1 else [a + x[0], *vec_scalar_add(a, x[1:])]


def vec_scalar_sub(a: int, x: List[int]) -> List[int]:
    # Subtract a scalar from each element in a vector.
    # x[i] = x[i] - a
    return [] if len(x) < 1 else [x[0] - a, *vec_scalar_sub(a, x[1:])]


def vec_scalar_mul(a: int, x: List[int]) -> List[int]:
    # Multiply a scalar with each element in a vector.
    return [] if len(x) < 1 else [a * x[0], *vec_scalar_mul(a, x[1:])]


def vec_scalar_div(a: int, x: List[int]) -> List[int]:
    # Divide each element of the vector by scalar 'a' using integer division.
    # x[i] = x[i] // a
    return [] if len(x) < 1 else [x[0] // a, *vec_scalar_div(a, x[1:])]


def scalar_vec_sub(a: int, x: List[int]) -> List[int]:
    # Subtract each element of the vector from scalar 'a'.
    # x[i] = a - x[i]
    return [] if len(x) < 1 else [a - x[0], *scalar_vec_sub(a, x[1:])]


def scalar_vec_div(a: int, x: List[int]) -> List[int]:
    # Divide scalar 'a' by each element of the vector using integer division.
    # x[i] = a // x[i]
    return [] if len(x) < 1 else [a // x[0], *scalar_vec_div(a, x[1:])]


def matrix_scalar_add(a: int, matrix_x: List[List[int]]) -> List[List[int]]:
    # Add a scalar to each element of the matrix.

    return (
        []
        if len(matrix_x) < 1
        else [vec_scalar_add(a, matrix_x[0]), *matrix_scalar_add(a, matrix_x[1:])]
    )


def matrix_vec_mul(matrix_x: List[List[int]], x: List[int]) -> List[int]:
    # Multiply a matrix with a vector.
    return (
        []
        if len(matrix_x) < 1 or len(matrix_x[0]) < 1 or not len(matrix_x[0]) == len(x)
        else [
            reduce_sum(vec_elemwise_mul(matrix_x[0], x)),
            *matrix_vec_mul(matrix_x[1:], x),
        ]
    )


def reduce_mul(x: List[int]) -> int:
    # Multiply all elements in a vector.
    return 1 if len(x) < 1 else x[0] * reduce_mul(x[1:])


def matrix_scalar_div(a: int, matrix_x: List[List[int]]) -> List[List[int]]:
    # Divide a scalar by each element of the matrix using integer division.
    # matrix_x[i][j] = matrix_x[i][j] // a
    return (
        []
        if len(matrix_x) < 1
        else [vec_scalar_div(a, matrix_x[0]), *matrix_scalar_div(a, matrix_x[1:])]
    )


def scalar_matrix_sub(a: int, matrix_x: List[List[int]]) -> List[List[int]]:
    # Subtract each element of the matrix from scalar 'a'.
    # matrix_x[i][j] = a - matrix_x[i][j]
    return (
        []
        if len(matrix_x) < 1
        else [scalar_vec_sub(a, matrix_x[0]), *scalar_matrix_sub(a, matrix_x[1:])]
    )


def scalar_matrix_div(a: int, matrix_x: List[List[int]]) -> List[List[int]]:
    # Divide scalar 'a' by each element of the matrix using integer division.
    # matrix_x[i][j] = a // matrix_x[i][j]
    return (
        []
        if len(matrix_x) < 1
        else [scalar_vec_div(a, matrix_x[0]), *scalar_matrix_div(a, matrix_x[1:])]
    )


def vec_map(x: List[int], map_int_to_int: Callable[[int], int]) -> List[int]:
    # Apply a mapping function to each element in a vector.
    return [] if len(x) < 1 else [map_int_to_int(x[0]), *vec_map(x[1:], map_int_to_int)]


def matrix_selection_two_args(
    matrix_x: List[List[int]],
    matrix_y: List[List[int]],
    select_two_args_arg: Callable[[int, int], int],
) -> List[List[int]]:
    # Apply a conditional selection function to each pair of elements in two matrices.
    return (
        []
        if len(matrix_x) < 1 or not len(matrix_x) == len(matrix_y)
        else [
            selection_two_args(matrix_x[0], matrix_y[0], select_two_args_arg),
            *matrix_selection_two_args(matrix_x[1:], matrix_y[1:], select_two_args_arg),
        ]
    )


def selection_two_args(
    x: List[int], y: List[int], select_two_args_arg: Callable[[int, int], int]
) -> List[int]:
    # Apply a conditional selection function to each pair of elements in two vectors.
    return (
        []
        if len(x) < 1 or not len(x) == len(y)
        else [
            select_two_args_arg(x[0], y[0]),
            *selection_two_args(x[1:], y[1:], select_two_args_arg),
        ]
    )


def vec_slice(lst: List[int], start: int, end: int) -> List[int]:
    # Slice a vector from start to end.
    return lst[:end][start:]


def matrix_row_slice(matrix: List[List[int]], start: int, end: int) -> List[List[int]]:
    # Slice rows of a matrix from index 'start' to 'end'
    return matrix[:end][start:]


def matrix_col_slice(matrix: List[List[int]], start: int, end: int) -> List[List[int]]:
    # Slice columns of a matrix from index 'start' to 'end'
    return (
        []
        if len(matrix) < 1
        else [matrix[0][start:end], *matrix_col_slice(matrix[1:], start, end)]
    )


def firsts(matrix: List[List[int]]) -> List[int]:
    # Helper function to get the first element of each row in a matrix.
    return [] if len(matrix) < 1 else [matrix[0][0], *firsts(matrix[1:])]


def rests(matrix: List[List[int]]) -> List[List[int]]:
    # Helper function to get the rest of the elements in each row in a matrix.
    return [] if len(matrix) < 1 else matrix_col_slice(matrix, 1, len(matrix[0]))


def matrix_elemwise_mul(
    matrix_x: List[List[int]], matrix_y: List[List[int]]
) -> List[List[int]]:
    # Element-wise multiplication of two matrices.
    return (
        []
        if len(matrix_x) < 1 or not len(matrix_x) == len(matrix_y)
        else [
            vec_elemwise_mul(matrix_x[0], matrix_y[0]),
            *matrix_elemwise_mul(matrix_x[1:], matrix_y[1:]),
        ]
    )
