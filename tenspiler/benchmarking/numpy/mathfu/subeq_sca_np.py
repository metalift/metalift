
####### import statements ########
import numpy as np

def subeq_sca_np (a, b, n):
    return (a[:n]) - (b)

def subeq_sca_np_glued (a, b, n):
    a = np.array(a).astype(np.int32)
    return subeq_sca_np(a, b, n)
