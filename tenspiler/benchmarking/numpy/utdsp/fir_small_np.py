
####### import statements ########
import numpy as np

def fir_small_np (NTAPS, input, coefficient):
    return np.sum((coefficient[:NTAPS]) * (input[:NTAPS]))

def fir_small_np_glued (NTAPS, input, coefficient):
    input = np.array(input).astype(np.int32)
    coefficient = np.array(coefficient).astype(np.int32)
    return fir_small_np(NTAPS, input, coefficient)
