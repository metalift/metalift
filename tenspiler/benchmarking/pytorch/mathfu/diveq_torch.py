
####### import statements ########
import torch

def diveq_torch (a, b, n):
    return (a[:n]) // (b[:n])

def diveq_torch_glued (a, b, n):
    a = torch.tensor(a, dtype=torch.int32)
    b = torch.tensor(b, dtype=torch.int32)
    return diveq_torch(a, b, n)
