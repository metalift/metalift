
####### import statements ########
import mlx.core as mx

def mag_array_mx (a, n):
    return mx.sum((a[:n]) * (a[:n]))

def mag_array_mx_glued (a, n):
    a = mx.array(a, mx.int32)
    return mag_array_mx(a, n)
