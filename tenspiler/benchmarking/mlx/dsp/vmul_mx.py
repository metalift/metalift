
####### import statements ########
import mlx.core as mx

def vmul_mx (a, b, n):
    return (b[:n]) * (a[:n])

def vmul_mx_glued (a, b, n):
    a = mx.array(a, mx.int32)
    b = mx.array(b, mx.int32)
    return vmul_mx(a, b, n)
