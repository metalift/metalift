####### import statements ########
import torch


def lmsfir1_torch(NTAPS, input, coefficient):
    return torch.sum((input[:NTAPS]) * (coefficient[:NTAPS]))


def lmsfir1_torch_glued(NTAPS, input, coefficient):
    input = torch.tensor(input, dtype=torch.int32)
    coefficient = torch.tensor(coefficient, dtype=torch.int32)
    return lmsfir1_torch(NTAPS, input, coefficient)
