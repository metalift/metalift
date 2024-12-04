####### import statements ########
import numpy as np


def cube_in_place_np(arr, n):
    return (arr[:n]) * ((arr[:n]) * (arr[:n]))


def cube_in_place_np_glued(arr, n):
    arr = np.array(arr).astype(np.int32)
    return cube_in_place_np(arr, n)
