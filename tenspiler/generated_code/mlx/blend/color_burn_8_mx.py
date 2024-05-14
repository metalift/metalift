
####### import statements ########
import mlx.core as mx

def color_burn_8_mx (base, active):
    return mx.where(mx.equal(active, 0), 32, (32) - (((32) - (base)) // (active)))

def color_burn_8_mx_glued (base, active):
    base = mx.array(base, mx.uint8)
    active = mx.array(active, mx.uint8)
    return color_burn_8_mx(base, active)
