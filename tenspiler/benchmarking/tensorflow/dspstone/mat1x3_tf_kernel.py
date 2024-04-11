
####### import statements ########
import tensorflow as tf

def mat1x3_tf(N, h, x):
    return tf.linalg.matvec(h[:N][:, 0:N], x[:N])

def mat1x3_tf_glued(N, h, x):
    h = tf.convert_to_tensor(h, dtype=tf.int32)
    x = tf.convert_to_tensor(x, dtype=tf.int32)
    return mat1x3_tf(N, h, x)

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

print("mat1x3_tf_kernel")
print(f"{np.average(times)} {np.std(times)}") 
