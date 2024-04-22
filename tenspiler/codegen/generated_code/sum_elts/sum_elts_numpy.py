####### import statements ########
import numpy as np


def sum_elts_np(arr, n):
    return np.sum(arr[:n])


def sum_elts_np_glued(arr, n):
    arr = np.array(arr).astype(np.int32)
    return sum_elts_np(arr, n)
