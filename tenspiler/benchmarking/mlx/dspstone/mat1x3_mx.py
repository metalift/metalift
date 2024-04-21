
####### import statements ########
import mlx.core as mx

def mat1x3_mx (N, h, x):
    return mx.matmul(h[:N][:, 0:N], x[:N])

def mat1x3_mx_glued (N, h, x):
    h = mx.array(h, mx.float32)
    x = mx.array(x, mx.float32)
    return mat1x3_mx(N, h, x)
