
####### import statements ########
import mlx.core as mx

def linear_burn_8_mx (base, active):
    return ((active) + (base)) - (32)

def linear_burn_8_mx_glued (base, active):
    base = mx.array(base, mx.uint8)
    active = mx.array(active, mx.uint8)
    return linear_burn_8_mx(base, active)
