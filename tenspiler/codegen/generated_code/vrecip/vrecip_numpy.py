####### import statements ########
import numpy as np


def vrecip_np(arr, n):
    return (1) // (arr[:n])


def vrecip_np_glued(arr, n):
    arr = np.array(arr).astype(np.int32)
    return vrecip_np(arr, n)
