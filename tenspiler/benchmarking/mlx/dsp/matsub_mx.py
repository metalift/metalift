
####### import statements ########
import mlx.core as mx

def matsub_mx (matA, matB, m, n):
    return (matA[:m][:, 0:n]) - (matB[:m][:, 0:n])

def matsub_mx_glued (matA, matB, m, n):
    matA = mx.array(matA, mx.int32)
    matB = mx.array(matB, mx.int32)
    return matsub_mx(matA, matB, m, n)
