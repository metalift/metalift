
####### import statements ########
import numpy as np

def mse_array_np (a, n):
    return np.sum((a[:n]) * (a[:n]))

def mse_array_np_glued (a, n):
    a = np.array(a).astype(np.int32)
    return mse_array_np(a, n)
