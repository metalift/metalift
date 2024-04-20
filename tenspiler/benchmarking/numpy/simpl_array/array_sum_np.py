
####### import statements ########
import numpy as np

def array_sum_np (arr, n):
    return np.sum(arr[:n])

def array_sum_np_glued (arr, n):
    arr = np.array(arr).astype(np.int32)
    return array_sum_np(arr, n)
