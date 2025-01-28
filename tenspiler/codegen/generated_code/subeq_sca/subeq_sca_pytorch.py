####### import statements ########
import torch


def subeq_sca_torch(a, b, n):
    return (a[:n]) - (b)


def subeq_sca_torch_glued(a, b, n):
    a = torch.tensor(a, dtype=torch.int32)
    return subeq_sca_torch(a, b, n)
