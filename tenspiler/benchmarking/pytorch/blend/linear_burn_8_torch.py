
####### import statements ########
import torch

def linear_burn_8_torch (base, active):
    return ((base) + (active)) - (255)

def linear_burn_8_torch_glued (base, active):
    base = torch.tensor(base, dtype=torch.uint8)
    active = torch.tensor(active, dtype=torch.uint8)
    return linear_burn_8_torch(base, active)
