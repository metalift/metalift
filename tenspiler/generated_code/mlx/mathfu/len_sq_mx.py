
####### import statements ########
import mlx.core as mx

def len_sq_mx (arr, n):
    return mx.sum((arr[:n]) * (arr[:n]))

def len_sq_mx_glued (arr, n):
    arr = mx.array(arr, mx.int32)
    return len_sq_mx(arr, n)
