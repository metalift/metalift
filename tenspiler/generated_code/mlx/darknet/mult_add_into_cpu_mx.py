
####### import statements ########
import mlx.core as mx

def mult_add_into_cpu_mx (N, X, Y, Z):
    return (Z[:N]) + ((X[:N]) * (Y[:N]))

def mult_add_into_cpu_mx_glued (N, X, Y, Z):
    X = mx.array(X, mx.int32)
    Y = mx.array(Y, mx.int32)
    Z = mx.array(Z, mx.int32)
    return mult_add_into_cpu_mx(N, X, Y, Z)
