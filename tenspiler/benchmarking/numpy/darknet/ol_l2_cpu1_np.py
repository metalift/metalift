
####### import statements ########
import numpy as np

def ol_l2_cpu1_np (n, pred, truth):
    return ((pred[:n]) - (truth[:n])) * ((pred[:n]) - (truth[:n]))

def ol_l2_cpu1_np_glued (n, pred, truth):
    pred = np.array(pred).astype(np.int32)
    truth = np.array(truth).astype(np.int32)
    return ol_l2_cpu1_np(n, pred, truth)
