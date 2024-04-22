####### import statements ########
import torch


def array_inc_torch(arr, n):
    return (1) + (arr[:n])


def array_inc_torch_glued(arr, n):
    arr = torch.tensor(arr, dtype=torch.int32)
    return array_inc_torch(arr, n)
