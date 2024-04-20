
####### import statements ########
import numpy as np

def color_dodge_8_np (base, active):
    return np.where(np.equal(active, 255), 255, (base) // ((255) - (active)))

def color_dodge_8_np_glued (base, active):
    base = np.array(base).astype(np.uint8)
    active = np.array(active).astype(np.uint8)
    return color_dodge_8_np(base, active)
