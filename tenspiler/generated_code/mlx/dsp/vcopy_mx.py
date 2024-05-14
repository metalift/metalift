
####### import statements ########
import mlx.core as mx

def vcopy_mx (a, n):
    return a[:n]

def vcopy_mx_glued (a, n):
    a = mx.array(a, mx.int32)
    return vcopy_mx(a, n)
