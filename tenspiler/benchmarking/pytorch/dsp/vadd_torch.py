
####### import statements ########
import torch

def vadd_torch (a, b, n):
    return (b[:n]) + (a[:n])

def vadd_torch_glued (a, b, n):
    a = torch.tensor(a, dtype=torch.int32)
    b = torch.tensor(b, dtype=torch.int32)
    return vadd_torch(a, b, n)
