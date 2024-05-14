
####### import statements ########
import torch

def n_real_updates_torch (N, A, B, C):
    return ((A[:N]) * (B[:N])) + (C[:N])

def n_real_updates_torch_glued (N, A, B, C):
    A = torch.tensor(A, dtype=torch.int32)
    B = torch.tensor(B, dtype=torch.int32)
    C = torch.tensor(C, dtype=torch.int32)
    return n_real_updates_torch(N, A, B, C)
