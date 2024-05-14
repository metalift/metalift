
####### import statements ########
import tensorflow as tf

def translate_array_tf(a, n, s):
    return (s) + (a[:n])

def translate_array_tf_glued(a, n, s):
    a = tf.convert_to_tensor(a, dtype=tf.int32)
    return translate_array_tf(a, n, s)
