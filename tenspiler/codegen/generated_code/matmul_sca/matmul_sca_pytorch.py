####### import statements ########
import torch


def matmul_sca_torch(matA, val, m, n):
    return (val) * (matA[:m][:, 0:n])


def matmul_sca_torch_glued(matA, val, m, n):
    matA = torch.tensor(matA, dtype=torch.int32)
    return matmul_sca_torch(matA, val, m, n)
