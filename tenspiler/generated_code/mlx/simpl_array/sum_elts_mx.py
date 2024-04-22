
####### import statements ########
import mlx.core as mx

def sum_elts_mx (arr, n):
    return mx.sum(arr[:n])

def sum_elts_mx_glued (arr, n):
    arr = mx.array(arr, mx.int32)
    return sum_elts_mx(arr, n)
