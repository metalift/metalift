
####### import statements ########
import mlx.core as mx

def softmax_part3_mx (output, max_pos):
    return mx.sum(output[:max_pos])

def softmax_part3_mx_glued (output, max_pos):
    output = mx.array(output, mx.float32)
    return softmax_part3_mx(output, max_pos)
