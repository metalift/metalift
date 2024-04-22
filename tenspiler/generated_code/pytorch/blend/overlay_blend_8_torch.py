
####### import statements ########
import torch

def overlay_blend_8_torch (base, active):
    return torch.where(torch.greater_equal(base, 128), ((((2) * (base)) + (base)) - ((((2) * (base)) * (base)) // (255))) - (255), (((2) * (base)) * (base)) // (255))

def overlay_blend_8_torch_glued (base, active):
    base = torch.tensor(base, dtype=torch.uint8)
    active = torch.tensor(active, dtype=torch.uint8)
    return overlay_blend_8_torch(base, active)
