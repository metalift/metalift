####### import statements ########
import tensorflow as tf


def n_real_updates_tf(N, A, B, C):
    return ((A[:N]) * (B[:N])) + (C[:N])


def n_real_updates_tf_glued(N, A, B, C):
    A = tf.convert_to_tensor(A, dtype=tf.int32)
    B = tf.convert_to_tensor(B, dtype=tf.int32)
    C = tf.convert_to_tensor(C, dtype=tf.int32)
    return n_real_updates_tf(N, A, B, C)
