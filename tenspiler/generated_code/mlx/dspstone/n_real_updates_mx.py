
####### import statements ########
import mlx.core as mx

def n_real_updates_mx (N, A, B, C):
    return ((B[:N]) * (A[:N])) + (C[:N])

def n_real_updates_mx_glued (N, A, B, C):
    A = mx.array(A, mx.int32)
    B = mx.array(B, mx.int32)
    C = mx.array(C, mx.int32)
    return n_real_updates_mx(N, A, B, C)
