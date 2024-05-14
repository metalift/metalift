
####### import statements ########
import mlx.core as mx

def matmul_mx (weight, input):
    return mx.matmul(weight, input)

def matmul_mx_glued (weight, input):
    weight = mx.array(weight, mx.float32)
    input = mx.array(input, mx.float32)
    return matmul_mx(weight, input)
