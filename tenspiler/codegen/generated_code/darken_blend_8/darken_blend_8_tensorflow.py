
####### import statements ########
import tensorflow as tf

def darken_blend_8_tf(base, active):
    return tf.where(tf.greater(active, base), base, active)

def darken_blend_8_tf_glued(base, active):
    base = tf.convert_to_tensor(base, dtype=tf.uint8)
    active = tf.convert_to_tensor(active, dtype=tf.uint8)
    return darken_blend_8_tf(base, active)
