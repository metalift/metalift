####### import statements ########
import torch


def color_dodge_8_torch(base, active):
    return torch.where(torch.eq(active, 32), 32, (base) // ((32) - (active)))


def color_dodge_8_torch_glued(base, active):
    base = torch.tensor(base, dtype=torch.uint8)
    active = torch.tensor(active, dtype=torch.uint8)
    return color_dodge_8_torch(base, active)
