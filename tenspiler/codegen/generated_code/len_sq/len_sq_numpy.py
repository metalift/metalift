####### import statements ########
import numpy as np


def len_sq_np(arr, n):
    return np.sum((arr[:n]) * (arr[:n]))


def len_sq_np_glued(arr, n):
    arr = np.array(arr).astype(np.int32)
    return len_sq_np(arr, n)
