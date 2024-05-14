
####### import statements ########
import numpy as np

def lighten_blend_8_np (base, active):
    return np.where(np.less(active, base), base, active)

def lighten_blend_8_np_glued (base, active):
    base = np.array(base).astype(np.uint8)
    active = np.array(active).astype(np.uint8)
    return lighten_blend_8_np(base, active)
