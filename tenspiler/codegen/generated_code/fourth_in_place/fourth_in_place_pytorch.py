####### import statements ########
import torch


def fourth_in_place_torch(arr, n):
    return ((arr[:n]) * (arr[:n])) * ((arr[:n]) * (arr[:n]))


def fourth_in_place_torch_glued(arr, n):
    arr = torch.tensor(arr, dtype=torch.int32)
    return fourth_in_place_torch(arr, n)
