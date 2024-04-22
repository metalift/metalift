####### import statements ########
import torch


def lmsfir2_torch(NTAPS, input, coefficient, error):
    return (coefficient[: (NTAPS) - (1)]) + ((error) * (input[: (NTAPS) - (1)]))


def lmsfir2_torch_glued(NTAPS, input, coefficient, error):
    input = torch.tensor(input, dtype=torch.int32)
    coefficient = torch.tensor(coefficient, dtype=torch.int32)
    return lmsfir2_torch(NTAPS, input, coefficient, error)
