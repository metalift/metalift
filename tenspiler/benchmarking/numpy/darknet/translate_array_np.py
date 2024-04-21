
####### import statements ########
import numpy as np

def translate_array_np (a, n, s):
    return (s) + (a[:n])

def translate_array_np_glued (a, n, s):
    a = np.array(a).astype(np.int32)
    return translate_array_np(a, n, s)
