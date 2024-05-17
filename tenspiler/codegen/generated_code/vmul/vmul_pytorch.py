
####### import statements ########
import torch

def vmul_torch (a, b, n):
    return (a[:n]) * (b[:n])

def vmul_torch_glued (a, b, n):
    a = torch.tensor(a, dtype=torch.int32)
    b = torch.tensor(b, dtype=torch.int32)
    return vmul_torch(a, b, n)
