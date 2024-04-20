
####### import statements ########
import mlx.core as mx

def vsub_mx (a, b, n):
    return (a[:n]) - (b[:n])

def vsub_mx_glued (a, b, n):
    a = mx.array(a, mx.int32)
    b = mx.array(b, mx.int32)
    return vsub_mx(a, b, n)
