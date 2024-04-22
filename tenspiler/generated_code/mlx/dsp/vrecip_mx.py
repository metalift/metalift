
####### import statements ########
import mlx.core as mx

def vrecip_mx (arr, n):
    return (1) // (arr[:n])

def vrecip_mx_glued (arr, n):
    arr = mx.array(arr, mx.int32)
    return vrecip_mx(arr, n)
