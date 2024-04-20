
####### import statements ########
import torch

def array_sum_torch (arr, n):
    return torch.sum(arr[:n])

def array_sum_torch_glued (arr, n):
    arr = torch.tensor(arr, dtype=torch.int32)
    return array_sum_torch(arr, n)
