
####### import statements ########
import torch

def vscal_torch (arr, v, n):
    return (v) * (arr[:n])

def vscal_torch_glued (arr, v, n):
    arr = torch.tensor(arr, dtype=torch.int32)
    return vscal_torch(arr, v, n)
