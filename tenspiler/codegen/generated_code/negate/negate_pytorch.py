####### import statements ########
import torch


def negate_torch(arr, n):
    return (0) - (arr[:n])


def negate_torch_glued(arr, n):
    arr = torch.tensor(arr, dtype=torch.int32)
    return negate_torch(arr, n)
