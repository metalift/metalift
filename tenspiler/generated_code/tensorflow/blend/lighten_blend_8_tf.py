
####### import statements ########
import tensorflow as tf

def lighten_blend_8_tf(base, active):
    return tf.where(tf.less(base, active), active, base)

def lighten_blend_8_tf_glued(base, active):
    base = tf.convert_to_tensor(base, dtype=tf.uint8)
    active = tf.convert_to_tensor(active, dtype=tf.uint8)
    return lighten_blend_8_tf(base, active)
