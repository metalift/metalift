
####### import statements ########
import mlx.core as mx

def overlay_blend_8_mx (base, active):
    return mx.where(mx.greater_equal(base, 16), ((((2) * (base)) + (base)) - ((((2) * (base)) * (base)) // (32))) - (32), (((2) * (base)) * (base)) // (32))

def overlay_blend_8_mx_glued (base, active):
    base = mx.array(base, mx.uint8)
    active = mx.array(active, mx.uint8)
    return overlay_blend_8_mx(base, active)
