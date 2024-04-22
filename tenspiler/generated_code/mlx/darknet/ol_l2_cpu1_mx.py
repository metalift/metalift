
####### import statements ########
import mlx.core as mx

def ol_l2_cpu1_mx (n, pred, truth):
    return ((pred[:n]) - (truth[:n])) * ((pred[:n]) - (truth[:n]))

def ol_l2_cpu1_mx_glued (n, pred, truth):
    pred = mx.array(pred, mx.int32)
    truth = mx.array(truth, mx.int32)
    return ol_l2_cpu1_mx(n, pred, truth)
