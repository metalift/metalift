
####### import statements ########
import mlx.core as mx

def ol_l2_cpu2_mx (n, pred, truth):
    return (truth[:n]) - (pred[:n])

def ol_l2_cpu2_mx_glued (n, pred, truth):
    pred = mx.array(pred, mx.int32)
    truth = mx.array(truth, mx.int32)
    return ol_l2_cpu2_mx(n, pred, truth)
