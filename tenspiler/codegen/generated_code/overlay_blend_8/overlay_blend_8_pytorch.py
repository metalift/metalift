
####### import statements ########
import torch

def overlay_blend_8_torch (base, active):
    return torch.where(torch.greater_equal(base, 16), ((((2) * (base)) + (base)) - ((((2) * (base)) * (base)) // (32))) - (32), (((2) * (base)) * (base)) // (32))

def overlay_blend_8_torch_glued (base, active):
    base = torch.tensor(base, dtype=torch.uint8)
    active = torch.tensor(active, dtype=torch.uint8)
    return overlay_blend_8_torch(base, active)
