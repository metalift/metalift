
####### import statements ########
import torch

def screen_blend_8_torch (base, active):
    return ((base) + (active)) - (((base) * (active)) // (32))

def screen_blend_8_torch_glued (base, active):
    base = torch.tensor(base, dtype=torch.uint8)
    active = torch.tensor(active, dtype=torch.uint8)
    return screen_blend_8_torch(base, active)
