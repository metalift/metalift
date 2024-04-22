
####### import statements ########
import mlx.core as mx

def vscal_mx (arr, v, n):
    return (v) * (arr[:n])

def vscal_mx_glued (arr, v, n):
    arr = mx.array(arr, mx.int32)
    return vscal_mx(arr, v, n)
