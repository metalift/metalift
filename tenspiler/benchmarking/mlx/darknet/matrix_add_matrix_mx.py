
####### import statements ########
import mlx.core as mx

def matrix_add_matrix_mx (from_matrix, to_matrix):
    return (to_matrix) + (from_matrix)

def matrix_add_matrix_mx_glued (from_matrix, to_matrix):
    from_matrix = mx.array(from_matrix, mx.int32)
    to_matrix = mx.array(to_matrix, mx.int32)
    return matrix_add_matrix_mx(from_matrix, to_matrix)
