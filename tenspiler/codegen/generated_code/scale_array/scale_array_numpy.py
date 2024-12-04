####### import statements ########
import numpy as np


def scale_array_np(a, n, s):
    return (s) * (a[:n])


def scale_array_np_glued(a, n, s):
    a = np.array(a).astype(np.int32)
    return scale_array_np(a, n, s)
