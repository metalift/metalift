
####### import statements ########
import torch

def vcopy_torch (a, n):
    return a[:n]

def vcopy_torch_glued (a, n):
    a = torch.tensor(a, dtype=torch.int32)
    return vcopy_torch(a, n)
