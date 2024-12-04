####### import statements ########
import torch


def ol_l2_cpu2_torch(n, pred, truth):
    return (truth[:n]) - (pred[:n])


def ol_l2_cpu2_torch_glued(n, pred, truth):
    pred = torch.tensor(pred, dtype=torch.int32)
    truth = torch.tensor(truth, dtype=torch.int32)
    return ol_l2_cpu2_torch(n, pred, truth)
