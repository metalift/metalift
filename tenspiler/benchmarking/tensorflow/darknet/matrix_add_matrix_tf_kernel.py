
####### import statements ########
import tensorflow as tf

def matrix_add_matrix_tf(from_matrix, to_matrix):
    return (to_matrix) + (from_matrix)

def matrix_add_matrix_tf_glued(from_matrix, to_matrix):
    from_matrix = tf.convert_to_tensor(from_matrix, dtype=tf.int32)
    to_matrix = tf.convert_to_tensor(to_matrix, dtype=tf.int32)
    return matrix_add_matrix_tf(from_matrix, to_matrix)

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

print("matrix_add_matrix_tf_kernel")
print(f"{np.average(times)} {np.std(times)}") 
