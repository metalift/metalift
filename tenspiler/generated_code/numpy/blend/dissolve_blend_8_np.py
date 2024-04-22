
####### import statements ########
import numpy as np

def dissolve_blend_8_np (base, active, opacity, rand_cons):
    return np.where((opacity) - ((((rand_cons) % (100)) + (1)) // (100)) >= 0, active, base)

def dissolve_blend_8_np_glued (base, active, opacity, rand_cons):
    base = np.array(base).astype(np.uint8)
    active = np.array(active).astype(np.uint8)
    return dissolve_blend_8_np(base, active, opacity, rand_cons)
