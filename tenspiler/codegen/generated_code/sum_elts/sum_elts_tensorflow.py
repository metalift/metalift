####### import statements ########
import tensorflow as tf


def sum_elts_tf(arr, n):
    return tf.reduce_sum(arr[:n])


def sum_elts_tf_glued(arr, n):
    arr = tf.convert_to_tensor(arr, dtype=tf.int32)
    return sum_elts_tf(arr, n)
