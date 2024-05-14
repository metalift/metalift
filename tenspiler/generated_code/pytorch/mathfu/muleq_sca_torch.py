
####### import statements ########
import torch

def muleq_sca_torch (a, b, n):
    return (b) * (a[:n])

def muleq_sca_torch_glued (a, b, n):
    a = torch.tensor(a, dtype=torch.int32)
    return muleq_sca_torch(a, b, n)
