####### import statements ########
import numpy as np


def softmax_part3_np(max_pos, output):
    return np.sum(output[:max_pos])


def softmax_part3_np_glued(max_pos, output):
    output = np.array(output).astype(np.float32)
    return softmax_part3_np(max_pos, output)
