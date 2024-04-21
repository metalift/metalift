
####### import statements ########
import torch

def normal_blend_f_torch (base, active, opacity):
    return ((opacity) * (active)) + (((1) - (opacity)) * (base))

def normal_blend_f_torch_glued (base, active, opacity):
    base = torch.tensor(base, dtype=torch.float32)
    active = torch.tensor(active, dtype=torch.float32)
    return normal_blend_f_torch(base, active, opacity)
