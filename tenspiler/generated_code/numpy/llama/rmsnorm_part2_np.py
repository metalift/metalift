
####### import statements ########
import numpy as np

def rmsnorm_part2_np (input, weight, ss):
    return ((1) / (np.sqrt(((ss) / (input.size)) + (1)))) * ((input) * (weight))

def rmsnorm_part2_np_glued (input, weight, ss):
    input = np.array(input).astype(np.float32)
    weight = np.array(weight).astype(np.float32)
    return rmsnorm_part2_np(input, weight, ss)
