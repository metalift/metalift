
####### import statements ########
import numpy as np

def color_burn_8_np (base, active):
    return np.where(np.equal(active, 0), 255, (255) - (((255) - (base)) // (active)))

def color_burn_8_np_glued (base, active):
    base = np.array(base).astype(np.uint8)
    active = np.array(active).astype(np.uint8)
    return color_burn_8_np(base, active)
