
####### import statements ########
import torch

def voffset_torch (arr, v, n):
    return (v) + (arr[:n])

def voffset_torch_glued (arr, v, n):
    arr = torch.tensor(arr, dtype=torch.int32)
    return voffset_torch(arr, v, n)
