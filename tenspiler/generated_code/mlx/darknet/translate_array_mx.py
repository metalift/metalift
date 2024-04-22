
####### import statements ########
import mlx.core as mx

def translate_array_mx (a, n, s):
    return (s) + (a[:n])

def translate_array_mx_glued (a, n, s):
    a = mx.array(a, mx.int32)
    return translate_array_mx(a, n, s)
