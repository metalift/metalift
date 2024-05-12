
####### import statements ########
import torch

def gemv_torch (M, N, A, x):
    return torch.matmul(A[:M][:, 0:N], x[:N])

def gemv_torch_glued (M, N, A, x):
    A = torch.tensor(A, dtype=torch.float32)
    x = torch.tensor(x, dtype=torch.float32)
    return gemv_torch(M, N, A, x)
