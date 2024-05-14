
####### import statements ########
import mlx.core as mx

def lmsfir1_mx (NTAPS, input, coefficient):
    return mx.sum((input[:NTAPS]) * (coefficient[:NTAPS]))

def lmsfir1_mx_glued (NTAPS, input, coefficient):
    input = mx.array(input, mx.int32)
    coefficient = mx.array(coefficient, mx.int32)
    return lmsfir1_mx(NTAPS, input, coefficient)
