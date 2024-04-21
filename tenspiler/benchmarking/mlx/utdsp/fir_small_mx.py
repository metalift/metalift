
####### import statements ########
import mlx.core as mx

def fir_small_mx (NTAPS, input, coefficient):
    return mx.sum((coefficient[:NTAPS]) * (input[:NTAPS]))

def fir_small_mx_glued (NTAPS, input, coefficient):
    input = mx.array(input, mx.int32)
    coefficient = mx.array(coefficient, mx.int32)
    return fir_small_mx(NTAPS, input, coefficient)
