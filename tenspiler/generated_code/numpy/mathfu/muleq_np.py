
####### import statements ########
import numpy as np

def muleq_np (a, b, n):
    return (a[:n]) * (b[:n])

def muleq_np_glued (a, b, n):
    a = np.array(a).astype(np.int32)
    b = np.array(b).astype(np.int32)
    return muleq_np(a, b, n)
