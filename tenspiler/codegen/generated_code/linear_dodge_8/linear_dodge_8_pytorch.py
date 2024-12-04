####### import statements ########
import torch


def linear_dodge_8_torch(base, active):
    return (base) + (active)


def linear_dodge_8_torch_glued(base, active):
    base = torch.tensor(base, dtype=torch.uint8)
    active = torch.tensor(active, dtype=torch.uint8)
    return linear_dodge_8_torch(base, active)
