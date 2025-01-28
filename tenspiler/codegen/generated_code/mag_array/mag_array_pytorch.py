####### import statements ########
import torch


def mag_array_torch(a, n):
    return torch.sum((a[:n]) * (a[:n]))


def mag_array_torch_glued(a, n):
    a = torch.tensor(a, dtype=torch.int32)
    return mag_array_torch(a, n)
