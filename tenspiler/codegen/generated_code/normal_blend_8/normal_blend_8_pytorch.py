####### import statements ########
import torch


def normal_blend_8_torch(base, active, opacity):
    return ((opacity) * (active)) + (((32) - (opacity)) * (base))


def normal_blend_8_torch_glued(base, active, opacity):
    base = torch.tensor(base, dtype=torch.uint8)
    active = torch.tensor(active, dtype=torch.uint8)
    return normal_blend_8_torch(base, active, opacity)
