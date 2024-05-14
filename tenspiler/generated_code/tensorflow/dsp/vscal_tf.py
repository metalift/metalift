
####### import statements ########
import tensorflow as tf

def vscal_tf(arr, v, n):
    return (v) * (arr[:n])

def vscal_tf_glued(arr, v, n):
    arr = tf.convert_to_tensor(arr, dtype=tf.int32)
    return vscal_tf(arr, v, n)
