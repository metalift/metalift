
####### import statements ########
import torch

def multiply_blend_8_torch (base, active):
    return ((base) * (active)) // (255)

def multiply_blend_8_torch_glued (base, active):
    base = torch.tensor(base, dtype=torch.uint8)
    active = torch.tensor(active, dtype=torch.uint8)
    return multiply_blend_8_torch(base, active)
