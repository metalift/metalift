####### import statements ########
import tensorflow as tf


def softmax_part4_tf(unnormalized_output, max_pos, sum):
    return (unnormalized_output[:max_pos]) / (sum)


def softmax_part4_tf_glued(unnormalized_output, max_pos, sum):
    unnormalized_output = tf.convert_to_tensor(unnormalized_output, dtype=tf.float32)
    return softmax_part4_tf(unnormalized_output, max_pos, sum)
