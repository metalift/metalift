
####### import statements ########
import torch

def subeq_torch (a, b, n):
    return (a[:n]) - (b[:n])

def subeq_torch_glued (a, b, n):
    a = torch.tensor(a, dtype=torch.int32)
    b = torch.tensor(b, dtype=torch.int32)
    return subeq_torch(a, b, n)
