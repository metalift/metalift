
####### import statements ########
import mlx.core as mx

def softmax_part4_mx (unnormalized_output, max_pos, sum):
    return (unnormalized_output[:max_pos]) / (sum)

def softmax_part4_mx_glued (unnormalized_output, max_pos, sum):
    unnormalized_output = mx.array(unnormalized_output, mx.float32)
    return softmax_part4_mx(unnormalized_output, max_pos, sum)
