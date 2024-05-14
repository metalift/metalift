
####### import statements ########
import mlx.core as mx

def array_sum_mx (arr, n):
    return mx.sum(arr[:n])

def array_sum_mx_glued (arr, n):
    arr = mx.array(arr, mx.int32)
    return array_sum_mx(arr, n)
