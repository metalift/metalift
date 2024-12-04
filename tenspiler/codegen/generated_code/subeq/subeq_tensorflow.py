####### import statements ########
import tensorflow as tf


def subeq_tf(a, b, n):
    return (a[:n]) - (b[:n])


def subeq_tf_glued(a, b, n):
    a = tf.convert_to_tensor(a, dtype=tf.int32)
    b = tf.convert_to_tensor(b, dtype=tf.int32)
    return subeq_tf(a, b, n)
