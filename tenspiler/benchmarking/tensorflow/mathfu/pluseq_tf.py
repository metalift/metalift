
####### import statements ########
import tensorflow as tf

def pluseq_tf(a, b, n):
    return (b[:n]) + (a[:n])

def pluseq_tf_glued(a, b, n):
    a = tf.convert_to_tensor(a, dtype=tf.int32)
    b = tf.convert_to_tensor(b, dtype=tf.int32)
    return pluseq_tf(a, b, n)
