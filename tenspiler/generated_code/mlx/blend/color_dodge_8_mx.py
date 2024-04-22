
####### import statements ########
import mlx.core as mx

def color_dodge_8_mx (base, active):
    return mx.where(mx.equal(active, 255), 255, (base) // ((255) - (active)))

def color_dodge_8_mx_glued (base, active):
    base = mx.array(base, mx.uint8)
    active = mx.array(active, mx.uint8)
    return color_dodge_8_mx(base, active)
