####### import statements ########
import numpy as np


def darken_blend_8_np(active, base):
    return np.where(np.greater(active, base), base, active)


def darken_blend_8_np_glued(active, base):
    active = np.array(active).astype(np.uint8)
    base = np.array(base).astype(np.uint8)
    return darken_blend_8_np(active, base)
