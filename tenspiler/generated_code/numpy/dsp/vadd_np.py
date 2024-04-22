
####### import statements ########
import numpy as np

def vadd_np (a, b, n):
    return (b[:n]) + (a[:n])

def vadd_np_glued (a, b, n):
    a = np.array(a).astype(np.int32)
    b = np.array(b).astype(np.int32)
    return vadd_np(a, b, n)
