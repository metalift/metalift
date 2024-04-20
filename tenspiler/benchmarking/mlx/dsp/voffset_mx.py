
####### import statements ########
import mlx.core as mx

def voffset_mx (arr, v, n):
    return (v) + (arr[:n])

def voffset_mx_glued (arr, v, n):
    arr = mx.array(arr, mx.int32)
    return voffset_mx(arr, v, n)
