
####### import statements ########
import mlx.core as mx

def gemv_mx (M, N, A, x):
    return mx.matmul(A[:M][:, 0:N], x[:N])

def gemv_mx_glued (M, N, A, x):
    A = mx.array(A, mx.float32)
    x = mx.array(x, mx.float32)
    return gemv_mx(M, N, A, x)
