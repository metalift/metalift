
####### import statements ########
import torch

def mat1x3_torch (N, h, x):
    return torch.matmul(h[:N][:, 0:N], x[:N])

def mat1x3_torch_glued (N, h, x):
    h = torch.tensor(h, dtype=torch.float32)
    x = torch.tensor(x, dtype=torch.float32)
    return mat1x3_torch(N, h, x)
