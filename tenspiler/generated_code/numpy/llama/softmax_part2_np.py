
####### import statements ########
import numpy as np

def softmax_part2_np (input, max_pos, max_val):
    return np.exp((input[:max_pos]) - (max_val))

def softmax_part2_np_glued (input, max_pos, max_val):
    input = np.array(input).astype(np.float32)
    return softmax_part2_np(input, max_pos, max_val)
