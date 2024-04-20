
####### import statements ########
import tensorflow as tf

def fourth_in_place_tf(arr, n):
    return ((arr[:n]) * (arr[:n])) * ((arr[:n]) * (arr[:n]))

def fourth_in_place_tf_glued(arr, n):
    arr = tf.convert_to_tensor(arr, dtype=tf.int32)
    return fourth_in_place_tf(arr, n)
