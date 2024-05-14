
####### import statements ########
import numpy as np

def softmax_part1_np (input, max_pos):
    return np.max(input[0:max_pos])

def softmax_part1_np_glued (input, max_pos):
    input = np.array(input).astype(np.float32)
    return softmax_part1_np(input, max_pos)
