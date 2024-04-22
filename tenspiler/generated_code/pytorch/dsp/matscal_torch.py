
####### import statements ########
import torch

def matscal_torch (mat, val, m, n):
    return (val) * (mat[:m][:, 0:n])

def matscal_torch_glued (mat, val, m, n):
    mat = torch.tensor(mat, dtype=torch.int32)
    return matscal_torch(mat, val, m, n)
