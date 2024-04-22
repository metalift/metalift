
####### import statements ########
import numpy as np

def softmax_part3_np (output, max_pos):
    return np.sum(output[:max_pos])

def softmax_part3_np_glued (output, max_pos):
    output = np.array(output).astype(np.float32)
    return softmax_part3_np(output, max_pos)
