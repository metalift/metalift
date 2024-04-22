
####### import statements ########
import numpy as np

def n_real_updates_np (N, A, B, C):
    return ((B[:N]) * (A[:N])) + (C[:N])

def n_real_updates_np_glued (N, A, B, C):
    A = np.array(A).astype(np.int32)
    B = np.array(B).astype(np.int32)
    C = np.array(C).astype(np.int32)
    return n_real_updates_np(N, A, B, C)
