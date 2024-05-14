
####### import statements ########
import numpy as np

def matmul_sca_np (matA, val, m, n):
    return (val) * (matA[:m][:, 0:n])

def matmul_sca_np_glued (matA, val, m, n):
    matA = np.array(matA).astype(np.int32)
    return matmul_sca_np(matA, val, m, n)
