####### import statements ########
import tensorflow as tf


def negate_tf(arr, n):
    return (0) - (arr[:n])


def negate_tf_glued(arr, n):
    arr = tf.convert_to_tensor(arr, dtype=tf.int32)
    return negate_tf(arr, n)
