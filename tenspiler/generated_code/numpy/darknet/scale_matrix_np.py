
####### import statements ########
import numpy as np

def scale_matrix_np (m, scale):
    return (scale) * (m)

def scale_matrix_np_glued (m, scale):
    m = np.array(m).astype(np.int32)
    return scale_matrix_np(m, scale)
