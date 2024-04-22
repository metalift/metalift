####### import statements ########
import numpy as np


def muleq_sca_np(a, b, n):
    return (b) * (a[:n])


def muleq_sca_np_glued(a, b, n):
    a = np.array(a).astype(np.int32)
    return muleq_sca_np(a, b, n)
