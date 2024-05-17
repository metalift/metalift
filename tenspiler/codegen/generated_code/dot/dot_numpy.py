
####### import statements ########
import numpy as np

def dot_np (a, b, n):
    return np.sum((a[:n]) * (b[:n]))

def dot_np_glued (a, b, n):
    a = np.array(a).astype(np.int32)
    b = np.array(b).astype(np.int32)
    return dot_np(a, b, n)
