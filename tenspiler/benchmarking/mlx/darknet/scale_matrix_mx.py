
####### import statements ########
import mlx.core as mx

def scale_matrix_mx (m, scale):
    return (scale) * (m)

def scale_matrix_mx_glued (m, scale):
    m = mx.array(m, mx.int32)
    return scale_matrix_mx(m, scale)
