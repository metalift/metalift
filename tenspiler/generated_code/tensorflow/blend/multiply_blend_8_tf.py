
####### import statements ########
import tensorflow as tf

def multiply_blend_8_tf(base, active):
    return ((base) * (active)) // (255)

def multiply_blend_8_tf_glued(base, active):
    base = tf.convert_to_tensor(base, dtype=tf.uint8)
    active = tf.convert_to_tensor(active, dtype=tf.uint8)
    return multiply_blend_8_tf(base, active)
