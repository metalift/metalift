
####### import statements ########
import numpy as np

def vscal_np (arr, v, n):
    return (v) * (arr[:n])

def vscal_np_glued (arr, v, n):
    arr = np.array(arr).astype(np.int32)
    return vscal_np(arr, v, n)
