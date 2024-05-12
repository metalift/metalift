
####### import statements ########
import torch

def matmul_torch (weight, input):
    return torch.matmul(weight, input)

def matmul_torch_glued (weight, input):
    weight = torch.tensor(weight, dtype=torch.float32)
    input = torch.tensor(input, dtype=torch.float32)
    return matmul_torch(weight, input)
