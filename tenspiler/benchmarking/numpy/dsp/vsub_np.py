
####### import statements ########
import numpy as np

def vsub_np (a, b, n):
    return (a[:n]) - (b[:n])

def vsub_np_glued (a, b, n):
    a = np.array(a).astype(np.int32)
    b = np.array(b).astype(np.int32)
    return vsub_np(a, b, n)
