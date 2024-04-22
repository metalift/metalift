
####### import statements ########
import numpy as np

def normal_blend_f_np (base, active, opacity):
    return ((opacity) * (active)) + (((1) - (opacity)) * (base))

def normal_blend_f_np_glued (base, active, opacity):
    base = np.array(base).astype(np.float32)
    active = np.array(active).astype(np.float32)
    return normal_blend_f_np(base, active, opacity)
