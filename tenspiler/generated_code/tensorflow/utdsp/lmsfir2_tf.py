
####### import statements ########
import tensorflow as tf

def lmsfir2_tf(NTAPS, input, coefficient, error):
    return (coefficient[:(NTAPS) - (1)]) + ((error) * (input[:(NTAPS) - (1)]))

def lmsfir2_tf_glued(NTAPS, input, coefficient, error):
    input = tf.convert_to_tensor(input, dtype=tf.int32)
    coefficient = tf.convert_to_tensor(coefficient, dtype=tf.int32)
    return lmsfir2_tf(NTAPS, input, coefficient, error)
