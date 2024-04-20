
####### import statements ########
import tensorflow as tf

def vrecip_tf(arr, n):
    return (1) // (arr[:n])

def vrecip_tf_glued(arr, n):
    arr = tf.convert_to_tensor(arr, dtype=tf.int32)
    return vrecip_tf(arr, n)
