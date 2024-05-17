
####### import statements ########
import numpy as np

def sum_of_squares_np (arr, n):
    return np.sum((arr[:n]) * (arr[:n]))

def sum_of_squares_np_glued (arr, n):
    arr = np.array(arr).astype(np.int32)
    return sum_of_squares_np(arr, n)
