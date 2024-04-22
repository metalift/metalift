
####### import statements ########
import mlx.core as mx

def vadd_mx (a, b, n):
    return (b[:n]) + (a[:n])

def vadd_mx_glued (a, b, n):
    a = mx.array(a, mx.int32)
    b = mx.array(b, mx.int32)
    return vadd_mx(a, b, n)
