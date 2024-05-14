
####### import statements ########
import mlx.core as mx

def wvec_mx (a, b, m, n):
    return ((m) * (a[:n])) + (b[:n])

def wvec_mx_glued (a, b, m, n):
    a = mx.array(a, mx.int32)
    b = mx.array(b, mx.int32)
    return wvec_mx(a, b, m, n)
