
####### import statements ########
import mlx.core as mx

def softmax_part1_mx (input, max_pos):
    return mx.max(input[:max_pos])

def softmax_part1_mx_glued (input, max_pos):
    input = mx.array(input, mx.float32)
    return softmax_part1_mx(input, max_pos)
