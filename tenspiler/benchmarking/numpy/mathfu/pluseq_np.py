
####### import statements ########
import numpy as np

def pluseq_np (a, b, n):
    return (b[:n]) + (a[:n])

def pluseq_np_glued (a, b, n):
    a = np.array(a).astype(np.int32)
    b = np.array(b).astype(np.int32)
    return pluseq_np(a, b, n)
