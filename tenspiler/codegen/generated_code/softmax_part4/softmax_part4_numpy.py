####### import statements ########
import numpy as np


def softmax_part4_np(unnormalized_output, max_pos, sum):
    return (unnormalized_output[:max_pos]) / (sum)


def softmax_part4_np_glued(unnormalized_output, max_pos, sum):
    unnormalized_output = np.array(unnormalized_output).astype(np.float32)
    return softmax_part4_np(unnormalized_output, max_pos, sum)
