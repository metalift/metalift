
####### import statements ########
import mlx.core as mx

def dissolve_blend_8_mx (base, active, opacity, rand_cons):
    return mx.where((opacity) - ((((rand_cons) % (100)) + (1)) // (100)) >= 0, active, base)

def dissolve_blend_8_mx_glued (base, active, opacity, rand_cons):
    base = mx.array(base, mx.uint8)
    active = mx.array(active, mx.uint8)
    return dissolve_blend_8_mx(base, active, opacity, rand_cons)
