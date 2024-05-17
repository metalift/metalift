
####### import statements ########
import torch

def translate_array_torch (a, n, s):
    return (s) + (a[:n])

def translate_array_torch_glued (a, n, s):
    a = torch.tensor(a, dtype=torch.int32)
    return translate_array_torch(a, n, s)
