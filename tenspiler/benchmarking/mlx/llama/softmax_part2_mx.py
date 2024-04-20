
####### import statements ########
import mlx.core as mx

def softmax_part2_mx (input, max_pos, max_val):
    return mx.exp((input[:max_pos]) - (max_val))

def softmax_part2_mx_glued (input, max_pos, max_val):
    input = mx.array(input, mx.float32)
    return softmax_part2_mx(input, max_pos, max_val)
