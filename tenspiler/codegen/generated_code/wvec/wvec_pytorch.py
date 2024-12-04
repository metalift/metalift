####### import statements ########
import torch


def wvec_torch(a, b, m, n):
    return ((m) * (a[:n])) + (b[:n])


def wvec_torch_glued(a, b, m, n):
    a = torch.tensor(a, dtype=torch.int32)
    b = torch.tensor(b, dtype=torch.int32)
    return wvec_torch(a, b, m, n)
