####### import statements ########
import torch


def vneg_torch(arr, n):
    return (0) - (arr[:n])


def vneg_torch_glued(arr, n):
    arr = torch.tensor(arr, dtype=torch.int32)
    return vneg_torch(arr, n)
