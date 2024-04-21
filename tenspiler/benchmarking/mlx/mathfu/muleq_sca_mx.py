
####### import statements ########
import mlx.core as mx

def muleq_sca_mx (a, b, n):
    return (b) * (a[:n])

def muleq_sca_mx_glued (a, b, n):
    a = mx.array(a, mx.int32)
    return muleq_sca_mx(a, b, n)
