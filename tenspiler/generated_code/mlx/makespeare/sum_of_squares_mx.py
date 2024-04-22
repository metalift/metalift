
####### import statements ########
import mlx.core as mx

def sum_of_squares_mx (arr, n):
    return mx.sum((arr[:n]) * (arr[:n]))

def sum_of_squares_mx_glued (arr, n):
    arr = mx.array(arr, mx.int32)
    return sum_of_squares_mx(arr, n)
