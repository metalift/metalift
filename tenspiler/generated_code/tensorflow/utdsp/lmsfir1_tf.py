
####### import statements ########
import tensorflow as tf

def lmsfir1_tf(NTAPS, input, coefficient):
    return tf.reduce_sum((coefficient[:NTAPS]) * (input[:NTAPS]))

def lmsfir1_tf_glued(NTAPS, input, coefficient):
    input = tf.convert_to_tensor(input, dtype=tf.int32)
    coefficient = tf.convert_to_tensor(coefficient, dtype=tf.int32)
    return lmsfir1_tf(NTAPS, input, coefficient)
