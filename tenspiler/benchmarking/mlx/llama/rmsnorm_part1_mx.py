
####### import statements ########
import mlx.core as mx

def rmsnorm_part1_mx (input, weight):
    return mx.sum((input) * (input))

def rmsnorm_part1_mx_glued (input, weight):
    input = mx.array(input, mx.float32)
    weight = mx.array(weight, mx.float32)
    return rmsnorm_part1_mx(input, weight)
