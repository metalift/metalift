
####### import statements ########
import mlx.core as mx

def mse_array_mx (a, n):
    return mx.sum((a[:n]) * (a[:n]))

def mse_array_mx_glued (a, n):
    a = mx.array(a, mx.int32)
    return mse_array_mx(a, n)
