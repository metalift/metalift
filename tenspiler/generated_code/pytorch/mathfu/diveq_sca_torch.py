
####### import statements ########
import torch

def diveq_sca_torch (a, b, n):
    return (a[:n]) // (b)

def diveq_sca_torch_glued (a, b, n):
    a = torch.tensor(a, dtype=torch.int32)
    return diveq_sca_torch(a, b, n)
