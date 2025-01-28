####### import statements ########
import numpy as np


def vmul_np(a, b, n):
    return (a[:n]) * (b[:n])


def vmul_np_glued(a, b, n):
    a = np.array(a).astype(np.int32)
    b = np.array(b).astype(np.int32)
    return vmul_np(a, b, n)
