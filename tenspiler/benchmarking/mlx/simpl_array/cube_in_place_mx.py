
####### import statements ########
import mlx.core as mx

def cube_in_place_mx (arr, n):
    return (arr[:n]) * ((arr[:n]) * (arr[:n]))

def cube_in_place_mx_glued (arr, n):
    arr = mx.array(arr, mx.int32)
    return cube_in_place_mx(arr, n)
