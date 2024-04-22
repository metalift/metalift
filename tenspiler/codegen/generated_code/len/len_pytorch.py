####### import statements ########
import torch


def len_torch(arr, n):
    return torch.sum((arr[:n]) * (arr[:n]))


def len_torch_glued(arr, n):
    arr = torch.tensor(arr, dtype=torch.int32)
    return len_torch(arr, n)
