####### import statements ########
import tensorflow as tf


def dot_tf(a, b, n):
    return tf.reduce_sum((a[:n]) * (b[:n]))


def dot_tf_glued(a, b, n):
    a = tf.convert_to_tensor(a, dtype=tf.int32)
    b = tf.convert_to_tensor(b, dtype=tf.int32)
    return dot_tf(a, b, n)
