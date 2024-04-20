
####### import statements ########
import mlx.core as mx

def dot_mx (a, b, n):
    return mx.sum((b[:n]) * (a[:n]))

def dot_mx_glued (a, b, n):
    a = mx.array(a, mx.int32)
    b = mx.array(b, mx.int32)
    return dot_mx(a, b, n)
