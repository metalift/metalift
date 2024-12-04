####### import statements ########
import tensorflow as tf


def transformer_part3_tf(input, hidden_dim):
    return (input[:hidden_dim]) * ((1) / ((1) + (tf.exp((0) - (input[:hidden_dim])))))


def transformer_part3_tf_glued(input, hidden_dim):
    input = tf.convert_to_tensor(input, dtype=tf.float32)
    return transformer_part3_tf(input, hidden_dim)
