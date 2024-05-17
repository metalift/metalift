
####### import statements ########
import numpy as np

def screen_blend_8_np (base, active):
    return ((base) + (active)) - (((base) * (active)) // (32))

def screen_blend_8_np_glued (base, active):
    base = np.array(base).astype(np.uint8)
    active = np.array(active).astype(np.uint8)
    return screen_blend_8_np(base, active)
