####### import statements ########
import tensorflow as tf


def diveq_sca_tf(a, b, n):
    return (a[:n]) // (b)


def diveq_sca_tf_glued(a, b, n):
    a = tf.convert_to_tensor(a, dtype=tf.int32)
    return diveq_sca_tf(a, b, n)
