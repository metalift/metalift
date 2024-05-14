
####### import statements ########
import numpy as np

def normal_blend_f_np (base, active, opacity):
    return ((opacity) * (active)) + (((1) - (opacity)) * (base))

def normal_blend_f_np_glued (base, active, opacity):
    base = np.array(base).astype(np.uint8)
    active = np.array(active).astype(np.uint8)
    return normal_blend_f_np(base, active, opacity)
