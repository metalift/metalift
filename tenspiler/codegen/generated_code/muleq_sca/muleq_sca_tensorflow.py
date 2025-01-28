####### import statements ########
import tensorflow as tf


def muleq_sca_tf(a, b, n):
    return (b) * (a[:n])


def muleq_sca_tf_glued(a, b, n):
    a = tf.convert_to_tensor(a, dtype=tf.int32)
    return muleq_sca_tf(a, b, n)
