####### import statements ########
import numpy as np


def array_inc_np(arr, n):
    return (1) + (arr[:n])


def array_inc_np_glued(arr, n):
    arr = np.array(arr).astype(np.int32)
    return array_inc_np(arr, n)
