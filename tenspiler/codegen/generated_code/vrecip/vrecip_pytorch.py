####### import statements ########
import torch


def vrecip_torch(arr, n):
    return (1) // (arr[:n])


def vrecip_torch_glued(arr, n):
    arr = torch.tensor(arr, dtype=torch.int32)
    return vrecip_torch(arr, n)
