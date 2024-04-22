####### import statements ########
import numpy as np


def gemv_np(M, N, A, x):
    return np.matmul(A[:M][:, 0:N], x[:N])


def gemv_np_glued(M, N, A, x):
    A = np.array(A).astype(np.int32)
    x = np.array(x).astype(np.int32)
    return gemv_np(M, N, A, x)
