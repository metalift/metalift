
####### import statements ########
import tensorflow as tf

def fir_small_tf(NTAPS, input, coefficient):
    return tf.reduce_sum((coefficient[:NTAPS]) * (input[:NTAPS]))

def fir_small_tf_glued(NTAPS, input, coefficient):
    input = tf.convert_to_tensor(input, dtype=tf.int32)
    coefficient = tf.convert_to_tensor(coefficient, dtype=tf.int32)
    return fir_small_tf(NTAPS, input, coefficient)

####### more import statements for benchmarking ########
import time
import cv2
import os
import numpy as np

####### setup for benchmarking ########
rng = np.random.default_rng(1)

folder = "./data/"

img_files = [os.path.join(folder, f) for f in os.listdir(folder) if os.path.isfile(os.path.join(folder, f))]

bases = []
actives = []

for _file in img_files:
    img = cv2.imread(_file, cv2.IMREAD_GRAYSCALE).astype(np.uint8)
    rnd = (rng.random(img.shape, dtype = np.float32) * 255).astype(np.uint8)
    bases.append(img)
    actives.append(rnd)

print("fir_small_tf_kernel")
print(f"{np.average(times)} {np.std(times)}") 
