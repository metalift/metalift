
####### import statements ########
import mlx.core as mx

def linear_dodge_8_mx (base, active):
    return (base) + (active)

def linear_dodge_8_mx_glued (base, active):
    base = mx.array(base, mx.uint8)
    active = mx.array(active, mx.uint8)
    return linear_dodge_8_mx(base, active)
