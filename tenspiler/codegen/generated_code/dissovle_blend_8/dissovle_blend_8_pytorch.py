
####### import statements ########
import torch

def dissolve_blend_8_torch (base, active, opacity, rand_cons):
    return torch.where(torch.tensor((opacity) - ((((rand_cons) % (100)) + (1)) / (100)) >= 0), active, base)

def dissolve_blend_8_torch_glued (base, active, opacity, rand_cons):
    base = torch.tensor(base, dtype=torch.float32)
    active = torch.tensor(active, dtype=torch.float32)
    return dissolve_blend_8_torch(base, active, opacity, rand_cons)
