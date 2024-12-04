####### import statements ########
import numpy as np


def voffset_np(arr, v, n):
    return (v) + (arr[:n])


def voffset_np_glued(arr, v, n):
    arr = np.array(arr).astype(np.int32)
    return voffset_np(arr, v, n)
