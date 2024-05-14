
####### import statements ########
import mlx.core as mx

def array_inc_mx (arr, n):
    return (1) + (arr[:n])

def array_inc_mx_glued (arr, n):
    arr = mx.array(arr, mx.int32)
    return array_inc_mx(arr, n)
