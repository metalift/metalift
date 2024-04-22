
####### import statements ########
import numpy as np

def darken_blend_8_np (base, active):
    return np.where(np.greater(base, active), active, base)

def darken_blend_8_np_glued (base, active):
    base = np.array(base).astype(np.uint8)
    active = np.array(active).astype(np.uint8)
    return darken_blend_8_np(base, active)
