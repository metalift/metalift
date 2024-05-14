
####### import statements ########
import torch

def sum_elts_torch (arr, n):
    return torch.sum(arr[:n])

def sum_elts_torch_glued (arr, n):
    arr = torch.tensor(arr, dtype=torch.int32)
    return sum_elts_torch(arr, n)
