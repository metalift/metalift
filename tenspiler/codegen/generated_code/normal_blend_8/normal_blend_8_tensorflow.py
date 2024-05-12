
####### import statements ########
import tensorflow as tf

def normal_blend_8_tf(base, active, opacity):
    return ((opacity) * (active)) + (((32) - (opacity)) * (base))

def normal_blend_8_tf_glued(base, active, opacity):
    base = tf.convert_to_tensor(base, dtype=tf.uint8)
    active = tf.convert_to_tensor(active, dtype=tf.uint8)
    return normal_blend_8_tf(base, active, opacity)
