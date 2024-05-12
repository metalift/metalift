
####### import statements ########
import numpy as np

def linear_burn_8_np (base, active):
    return ((base) + (active)) - (32)

def linear_burn_8_np_glued (base, active):
    base = np.array(base).astype(np.uint8)
    active = np.array(active).astype(np.uint8)
    return linear_burn_8_np(base, active)
