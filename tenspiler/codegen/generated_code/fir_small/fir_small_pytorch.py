####### import statements ########
import torch


def fir_small_torch(NTAPS, input, coefficient):
    return torch.sum((input[:NTAPS]) * (coefficient[:NTAPS]))


def fir_small_torch_glued(NTAPS, input, coefficient):
    input = torch.tensor(input, dtype=torch.int32)
    coefficient = torch.tensor(coefficient, dtype=torch.int32)
    return fir_small_torch(NTAPS, input, coefficient)
