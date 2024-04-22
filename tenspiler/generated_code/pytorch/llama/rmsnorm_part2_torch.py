
####### import statements ########
import torch

def rmsnorm_part2_torch (input, weight, ss):
    return ((1) / (torch.sqrt(torch.as_tensor(((ss) / (input.size(dim=0))) + (1))))) * ((input) * (weight))

def rmsnorm_part2_torch_glued (input, weight, ss):
    input = torch.tensor(input, dtype=torch.float32)
    weight = torch.tensor(weight, dtype=torch.float32)
    return rmsnorm_part2_torch(input, weight, ss)
