
####### import statements ########
import numpy as np

def sum_array_np (a, n):
    return np.sum(a[:n])

def sum_array_np_glued (a, n):
    a = np.array(a).astype(np.int32)
    return sum_array_np(a, n)
