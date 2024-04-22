####### import statements ########
import torch


def mult_add_into_cpu_torch(N, X, Y, Z):
    return (Z[:N]) + ((X[:N]) * (Y[:N]))


def mult_add_into_cpu_torch_glued(N, X, Y, Z):
    X = torch.tensor(X, dtype=torch.int32)
    Y = torch.tensor(Y, dtype=torch.int32)
    Z = torch.tensor(Z, dtype=torch.int32)
    return mult_add_into_cpu_torch(N, X, Y, Z)
