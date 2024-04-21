
####### import statements ########
import mlx.core as mx

def matscal_mx (mat, val, m, n):
    return (val) * (mat[:m][:, 0:n])

def matscal_mx_glued (mat, val, m, n):
    mat = mx.array(mat, mx.int32)
    return matscal_mx(mat, val, m, n)
