
####### import statements ########
import torch

def color_burn_8_torch (base, active):
    return torch.where(torch.eq(active, 0), 255, (255) - (((255) - (base)) // (active)))

def color_burn_8_torch_glued (base, active):
    base = torch.tensor(base, dtype=torch.uint8)
    active = torch.tensor(active, dtype=torch.uint8)
    return color_burn_8_torch(base, active)
