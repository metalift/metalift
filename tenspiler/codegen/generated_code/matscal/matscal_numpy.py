####### import statements ########
import numpy as np


def matscal_np(mat, val, m, n):
    return (val) * (mat[:m][:, 0:n])


def matscal_np_glued(mat, val, m, n):
    mat = np.array(mat).astype(np.int32)
    return matscal_np(mat, val, m, n)
