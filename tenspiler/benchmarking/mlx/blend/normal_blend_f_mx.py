
####### import statements ########
import mlx.core as mx

def normal_blend_f_mx (base, active, opacity):
    return ((opacity) * (active)) + (((1) - (opacity)) * (base))

def normal_blend_f_mx_glued (base, active, opacity):
    base = mx.array(base, mx.float32)
    active = mx.array(active, mx.float32)
    return normal_blend_f_mx(base, active, opacity)
