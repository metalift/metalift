####### import statements ########
import numpy as np


def multiply_blend_8_np(base, active):
    return ((base) * (active)) // (32)


def multiply_blend_8_np_glued(base, active):
    base = np.array(base).astype(np.uint8)
    active = np.array(active).astype(np.uint8)
    return multiply_blend_8_np(base, active)
