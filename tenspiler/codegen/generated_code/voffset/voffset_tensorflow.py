####### import statements ########
import tensorflow as tf


def voffset_tf(arr, v, n):
    return (v) + (arr[:n])


def voffset_tf_glued(arr, v, n):
    arr = tf.convert_to_tensor(arr, dtype=tf.int32)
    return voffset_tf(arr, v, n)
