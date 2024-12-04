####### import statements ########
import numpy as np


def vneg_np(arr, n):
    return (0) - (arr[:n])


def vneg_np_glued(arr, n):
    arr = np.array(arr).astype(np.int32)
    return vneg_np(arr, n)
