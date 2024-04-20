
####### import statements ########
import mlx.core as mx

def matmul_sca_mx (matA, val, m, n):
    return (val) * (matA[:m][:, 0:n])

def matmul_sca_mx_glued (matA, val, m, n):
    matA = mx.array(matA, mx.int32)
    return matmul_sca_mx(matA, val, m, n)
