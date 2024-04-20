
####### import statements ########
import torch

def vsub_torch (a, b, n):
    return (a[:n]) - (b[:n])

def vsub_torch_glued (a, b, n):
    a = torch.tensor(a, dtype=torch.int32)
    b = torch.tensor(b, dtype=torch.int32)
    return vsub_torch(a, b, n)
