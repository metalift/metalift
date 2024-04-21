
####### import statements ########
import tensorflow as tf

def wvec_tf(a, b, m, n):
    return ((m) * (a[:n])) + (b[:n])

def wvec_tf_glued(a, b, m, n):
    a = tf.convert_to_tensor(a, dtype=tf.int32)
    b = tf.convert_to_tensor(b, dtype=tf.int32)
    return wvec_tf(a, b, m, n)
