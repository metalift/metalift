####### import statements ########
import numpy as np


def vcopy_np(a, n):
    return a[:n]


def vcopy_np_glued(a, n):
    a = np.array(a).astype(np.int32)
    return vcopy_np(a, n)
