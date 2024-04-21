
####### import statements ########
import mlx.core as mx

def subeq_sca_mx (a, b, n):
    return (a[:n]) - (b)

def subeq_sca_mx_glued (a, b, n):
    a = mx.array(a, mx.int32)
    return subeq_sca_mx(a, b, n)
