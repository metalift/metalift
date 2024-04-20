
####### import statements ########
import numpy as np

def len_np (arr, n):
    return np.sum((arr[:n]) * (arr[:n]))

def len_np_glued (arr, n):
    arr = np.array(arr).astype(np.int32)
    return len_np(arr, n)
