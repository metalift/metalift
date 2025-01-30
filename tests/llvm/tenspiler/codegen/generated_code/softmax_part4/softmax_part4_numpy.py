####### import statements ########
import numpy as np


def softmax_part4_np(max_pos, sum, unnormalized_output):
    return (unnormalized_output[:max_pos]) / (sum)


def softmax_part4_np_glued(max_pos, sum, unnormalized_output):
    unnormalized_output = np.array(unnormalized_output).astype(np.float32)
    return softmax_part4_np(max_pos, sum, unnormalized_output)
