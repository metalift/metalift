
####### import statements ########
import tensorflow as tf

def ol_l2_cpu2_tf(n, pred, truth):
    return (truth[:n]) - (pred[:n])

def ol_l2_cpu2_tf_glued(n, pred, truth):
    pred = tf.convert_to_tensor(pred, dtype=tf.int32)
    truth = tf.convert_to_tensor(truth, dtype=tf.int32)
    return ol_l2_cpu2_tf(n, pred, truth)
