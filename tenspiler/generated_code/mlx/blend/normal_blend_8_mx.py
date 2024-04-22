
####### import statements ########
import mlx.core as mx

def normal_blend_8_mx (base, active, opacity):
    return ((opacity) * (active)) + (((255) - (opacity)) * (base))

def normal_blend_8_mx_glued (base, active, opacity):
    base = mx.array(base, mx.uint8)
    active = mx.array(active, mx.uint8)
    return normal_blend_8_mx(base, active, opacity)
