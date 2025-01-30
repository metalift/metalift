####### import statements ########
import numpy as np


def multiply_blend_8_np(active, base):
    return ((base) * (active)) // (32)


def multiply_blend_8_np_glued(active, base):
    active = np.array(active).astype(np.uint8)
    base = np.array(base).astype(np.uint8)
    return multiply_blend_8_np(active, base)
