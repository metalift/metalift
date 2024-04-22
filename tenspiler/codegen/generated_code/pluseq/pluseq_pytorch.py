####### import statements ########
import torch


def pluseq_torch(a, b, n):
    return (b[:n]) + (a[:n])


def pluseq_torch_glued(a, b, n):
    a = torch.tensor(a, dtype=torch.int32)
    b = torch.tensor(b, dtype=torch.int32)
    return pluseq_torch(a, b, n)
