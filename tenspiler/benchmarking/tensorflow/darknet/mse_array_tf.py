####### import statements ########
import tensorflow as tf


def mse_array_tf(a, n):
    return tf.reduce_sum((a[:n]) * (a[:n]))


def mse_array_tf_glued(a, n):
    a = tf.convert_to_tensor(a, dtype=tf.int32)
    return mse_array_tf(a, n)


import os

####### more import statements for benchmarking ########
import time

import cv2
import numpy as np

####### setup for benchmarking ########
gpus = tf.config.list_physical_devices("GPU")
if not gpus:
    print("No GPU is available")
rng = np.random.default_rng(1)

folder = "./data/"

img_files = [
    os.path.join(folder, f)
    for f in os.listdir(folder)
    if os.path.isfile(os.path.join(folder, f))
]

bases = []
actives = []

for _file in img_files:
    img = cv2.imread(_file, cv2.IMREAD_GRAYSCALE).astype(np.uint8)
    rnd = (rng.random(img.shape, dtype=np.float32) * 255).astype(np.uint8)
    bases.append(img)
    actives.append(rnd)

####### runner. need to manually update for each file ########
runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(bases)):
        b = bases[i].flatten().astype(np.int32)

        with tf.device("/CPU:0"):
            b = tf.convert_to_tensor(b, np.int32)

            (n,) = b.shape

        with tf.device("/GPU:0"):
            start_time = time.perf_counter()

            b = tf.identity(b)
            res = mse_array_tf(b, n)
        with tf.device("/CPU:0"):
            res = tf.identity(res)
            end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("mse_array_tf")
print(f"{np.average(times)} {np.std(times)}")

times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(bases)):
        b = bases[i].flatten().astype(np.int32)

        with tf.device("/GPU:0"):
            b = tf.convert_to_tensor(b, np.int32)

            (n,) = b.shape

            start_time = time.perf_counter()
            mse_array_tf(b, n)

            end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print(f"{np.average(times)} {np.std(times)}")
