
####### import statements ########
import mlx.core as mx

def darken_blend_8_mx (base, active):
    return mx.where(mx.greater(base, active), active, base)

def darken_blend_8_mx_glued (base, active):
    base = mx.array(base, mx.uint8)
    active = mx.array(active, mx.uint8)
    return darken_blend_8_mx(base, active)
