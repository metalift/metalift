
####### import statements ########
import tensorflow as tf

def n_real_updates_tf(N, A, B, C):
    return ((B[:N]) * (A[:N])) + (C[:N])

def n_real_updates_tf_glued(N, A, B, C):
    A = tf.convert_to_tensor(A, dtype=tf.int32)
    B = tf.convert_to_tensor(B, dtype=tf.int32)
    C = tf.convert_to_tensor(C, dtype=tf.int32)
    return n_real_updates_tf(N, A, B, C)

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

print("n_real_updates_tf_kernel")
print(f"{np.average(times)} {np.std(times)}") 
