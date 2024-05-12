
####### import statements ########
import tensorflow as tf

def mse_array_tf(a, n):
    return tf.reduce_sum((a[:n]) * (a[:n]))

def mse_array_tf_glued(a, n):
    a = tf.convert_to_tensor(a, dtype=tf.int32)
    return mse_array_tf(a, n)
