
####### import statements ########
import mlx.core as mx

def sum_array_mx (a, n):
    return mx.sum(a[:n])

def sum_array_mx_glued (a, n):
    a = mx.array(a, mx.int32)
    return sum_array_mx(a, n)
