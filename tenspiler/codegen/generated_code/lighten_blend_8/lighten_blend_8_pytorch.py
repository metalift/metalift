####### import statements ########
import torch


def lighten_blend_8_torch(base, active):
    return torch.where(torch.less(active, base), base, active)


def lighten_blend_8_torch_glued(base, active):
    base = torch.tensor(base, dtype=torch.uint8)
    active = torch.tensor(active, dtype=torch.uint8)
    return lighten_blend_8_torch(base, active)
