####### import statements ########
import numpy as np


def diveq_sca_np(a, b, n):
    return (a[:n]) // (b)


def diveq_sca_np_glued(a, b, n):
    a = np.array(a).astype(np.int32)
    return diveq_sca_np(a, b, n)
