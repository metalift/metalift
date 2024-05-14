
####### import statements ########
import mlx.core as mx

def lighten_blend_8_mx (base, active):
    return mx.where(mx.less(active, base), base, active)

def lighten_blend_8_mx_glued (base, active):
    base = mx.array(base, mx.uint8)
    active = mx.array(active, mx.uint8)
    return lighten_blend_8_mx(base, active)
