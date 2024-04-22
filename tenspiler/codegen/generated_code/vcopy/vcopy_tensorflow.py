####### import statements ########
import tensorflow as tf


def vcopy_tf(a, n):
    return a[:n]


def vcopy_tf_glued(a, n):
    a = tf.convert_to_tensor(a, dtype=tf.int32)
    return vcopy_tf(a, n)
