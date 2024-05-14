
####### import statements ########
import mlx.core as mx

def negate_mx (arr, n):
    return (0) - (arr[:n])

def negate_mx_glued (arr, n):
    arr = mx.array(arr, mx.int32)
    return negate_mx(arr, n)
