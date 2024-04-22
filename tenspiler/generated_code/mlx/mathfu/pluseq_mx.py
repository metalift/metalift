
####### import statements ########
import mlx.core as mx

def pluseq_mx (a, b, n):
    return (b[:n]) + (a[:n])

def pluseq_mx_glued (a, b, n):
    a = mx.array(a, mx.int32)
    b = mx.array(b, mx.int32)
    return pluseq_mx(a, b, n)
