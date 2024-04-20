
####### import statements ########
import torch

def cube_in_place_torch (arr, n):
    return (arr[:n]) * ((arr[:n]) * (arr[:n]))

def cube_in_place_torch_glued (arr, n):
    arr = torch.tensor(arr, dtype=torch.int32)
    return cube_in_place_torch(arr, n)
