####### import statements ########
import numpy as np


def wvec_np(a, b, m, n):
    return ((m) * (a[:n])) + (b[:n])


def wvec_np_glued(a, b, m, n):
    a = np.array(a).astype(np.int32)
    b = np.array(b).astype(np.int32)
    return wvec_np(a, b, m, n)
