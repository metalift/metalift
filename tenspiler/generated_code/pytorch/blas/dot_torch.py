
####### import statements ########
import torch

def dot_torch (a, b, n):
    return torch.sum((b[:n]) * (a[:n]))

def dot_torch_glued (a, b, n):
    a = torch.tensor(a, dtype=torch.int32)
    b = torch.tensor(b, dtype=torch.int32)
    return dot_torch(a, b, n)
