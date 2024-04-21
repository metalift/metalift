
####### import statements ########
import torch

def mse_array_torch (a, n):
    return torch.sum((a[:n]) * (a[:n]))

def mse_array_torch_glued (a, n):
    a = torch.tensor(a, dtype=torch.int32)
    return mse_array_torch(a, n)
