
####### import statements ########
import mlx.core as mx

def vneg_mx (arr, n):
    return (0) - (arr[:n])

def vneg_mx_glued (arr, n):
    arr = mx.array(arr, mx.int32)
    return vneg_mx(arr, n)
