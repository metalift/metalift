####### import statements ########
import tensorflow as tf


def vneg_tf(arr, n):
    return (0) - (arr[:n])


def vneg_tf_glued(arr, n):
    arr = tf.convert_to_tensor(arr, dtype=tf.int32)
    return vneg_tf(arr, n)
