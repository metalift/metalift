####### import statements ########
import numpy as np


def rmsnorm_part1_np(input, weight):
    return np.sum((input) * (input))


def rmsnorm_part1_np_glued(input, weight):
    input = np.array(input).astype(np.float32)
    weight = np.array(weight).astype(np.float32)
    return rmsnorm_part1_np(input, weight)
