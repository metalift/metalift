
####### import statements ########
import tensorflow as tf

def transformer_part4_tf(input1, input2, hidden_dim):
    return (input1[:hidden_dim]) * (input2[:hidden_dim])

def transformer_part4_tf_glued(input1, input2, hidden_dim):
    input1 = tf.convert_to_tensor(input1, dtype=tf.float32)
    input2 = tf.convert_to_tensor(input2, dtype=tf.float32)
    return transformer_part4_tf(input1, input2, hidden_dim)
