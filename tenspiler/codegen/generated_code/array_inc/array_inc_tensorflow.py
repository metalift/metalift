####### import statements ########
import tensorflow as tf


def array_inc_tf(arr, n):
    return (1) + (arr[:n])


def array_inc_tf_glued(arr, n):
    arr = tf.convert_to_tensor(arr, dtype=tf.int32)
    return array_inc_tf(arr, n)
