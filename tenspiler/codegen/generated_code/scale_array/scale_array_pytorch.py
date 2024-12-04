####### import statements ########
import torch


def scale_array_torch(a, n, s):
    return (s) * (a[:n])


def scale_array_torch_glued(a, n, s):
    a = torch.tensor(a, dtype=torch.int32)
    return scale_array_torch(a, n, s)
