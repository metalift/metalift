####### import statements ########
import torch


def len_sq_torch(arr, n):
    return torch.sum((arr[:n]) * (arr[:n]))


def len_sq_torch_glued(arr, n):
    arr = torch.tensor(arr, dtype=torch.int32)
    return len_sq_torch(arr, n)
