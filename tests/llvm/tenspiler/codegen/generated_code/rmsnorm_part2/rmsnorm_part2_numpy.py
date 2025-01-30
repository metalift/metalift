####### import statements ########
import numpy as np


def rmsnorm_part2_np(input, ss, weight):
    return ((1) / (np.sqrt(((ss) / (input.size)) + (1)))) * ((weight) * (input))


def rmsnorm_part2_np_glued(input, ss, weight):
    input = np.array(input).astype(np.float32)
    weight = np.array(weight).astype(np.float32)
    return rmsnorm_part2_np(input, ss, weight)
