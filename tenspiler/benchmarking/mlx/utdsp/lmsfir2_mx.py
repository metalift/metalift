
####### import statements ########
import mlx.core as mx

def lmsfir2_mx (NTAPS, input, coefficient, error):
    return (coefficient[:(NTAPS) - (1)]) + ((error) * (input[:(NTAPS) - (1)]))

def lmsfir2_mx_glued (NTAPS, input, coefficient, error):
    input = mx.array(input, mx.int32)
    coefficient = mx.array(coefficient, mx.int32)
    return lmsfir2_mx(NTAPS, input, coefficient, error)
