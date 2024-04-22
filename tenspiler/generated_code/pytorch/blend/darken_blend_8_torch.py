
####### import statements ########
import torch

def darken_blend_8_torch (base, active):
    return torch.where(torch.greater(base, active), active, base)

def darken_blend_8_torch_glued (base, active):
    base = torch.tensor(base, dtype=torch.uint8)
    active = torch.tensor(active, dtype=torch.uint8)
    return darken_blend_8_torch(base, active)
