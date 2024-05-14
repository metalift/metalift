
####### import statements ########
import torch

def sum_of_squares_torch (arr, n):
    return torch.sum((arr[:n]) * (arr[:n]))

def sum_of_squares_torch_glued (arr, n):
    arr = torch.tensor(arr, dtype=torch.int32)
    return sum_of_squares_torch(arr, n)
