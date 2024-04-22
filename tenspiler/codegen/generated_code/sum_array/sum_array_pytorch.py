####### import statements ########
import torch


def sum_array_torch(a, n):
    return torch.sum(a[:n])


def sum_array_torch_glued(a, n):
    a = torch.tensor(a, dtype=torch.int32)
    return sum_array_torch(a, n)
