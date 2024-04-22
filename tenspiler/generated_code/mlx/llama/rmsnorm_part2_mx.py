
####### import statements ########
import mlx.core as mx

def rmsnorm_part2_mx (input, weight, ss):
    return ((1) / (mx.sqrt(mx.array(((ss) / (input.size)) + (1))))) * ((input) * (weight))

def rmsnorm_part2_mx_glued (input, weight, ss):
    input = mx.array(input, mx.float32)
    weight = mx.array(weight, mx.float32)
    return rmsnorm_part2_mx(input, weight, ss)
