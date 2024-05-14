
####### import statements ########
import mlx.core as mx

def muleq_mx (a, b, n):
    return (a[:n]) * (b[:n])

def muleq_mx_glued (a, b, n):
    a = mx.array(a, mx.int32)
    b = mx.array(b, mx.int32)
    return muleq_mx(a, b, n)
