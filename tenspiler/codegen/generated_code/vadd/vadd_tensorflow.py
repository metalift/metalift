####### import statements ########
import tensorflow as tf


def vadd_tf(a, b, n):
    return (b[:n]) + (a[:n])


def vadd_tf_glued(a, b, n):
    a = tf.convert_to_tensor(a, dtype=tf.int32)
    b = tf.convert_to_tensor(b, dtype=tf.int32)
    return vadd_tf(a, b, n)
