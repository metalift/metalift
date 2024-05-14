
####### import statements ########
import tensorflow as tf

def array_sum_tf(arr, n):
    return tf.reduce_sum(arr[:n])

def array_sum_tf_glued(arr, n):
    arr = tf.convert_to_tensor(arr, dtype=tf.int32)
    return array_sum_tf(arr, n)
