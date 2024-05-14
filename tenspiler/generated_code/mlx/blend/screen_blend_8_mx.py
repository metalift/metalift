
####### import statements ########
import mlx.core as mx

def screen_blend_8_mx (base, active):
    return ((base) + (active)) - (((base) * (active)) // (32))

def screen_blend_8_mx_glued (base, active):
    base = mx.array(base, mx.uint8)
    active = mx.array(active, mx.uint8)
    return screen_blend_8_mx(base, active)
