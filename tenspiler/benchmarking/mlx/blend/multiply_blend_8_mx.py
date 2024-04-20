
####### import statements ########
import mlx.core as mx

def multiply_blend_8_mx (base, active):
    return ((base) * (active)) // (255)

def multiply_blend_8_mx_glued (base, active):
    base = mx.array(base, mx.uint8)
    active = mx.array(active, mx.uint8)
    return multiply_blend_8_mx(base, active)
