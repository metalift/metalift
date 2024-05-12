
####### import statements ########
import torch

def rmsnorm_part1_torch (input, weight):
    return torch.sum((input) * (input))

def rmsnorm_part1_torch_glued (input, weight):
    input = torch.tensor(input, dtype=torch.float32)
    weight = torch.tensor(weight, dtype=torch.float32)
    return rmsnorm_part1_torch(input, weight)
