
####### import statements ########
import torch

def matsub_torch (matA, matB, m, n):
    return (matA[:m][:, 0:n]) - (matB[:m][:, 0:n])

def matsub_torch_glued (matA, matB, m, n):
    matA = torch.tensor(matA, dtype=torch.int32)
    matB = torch.tensor(matB, dtype=torch.int32)
    return matsub_torch(matA, matB, m, n)
