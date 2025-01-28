####### import statements ########
import numpy as np


def negate_np(arr, n):
    return (0) - (arr[:n])


def negate_np_glued(arr, n):
    arr = np.array(arr).astype(np.int32)
    return negate_np(arr, n)
