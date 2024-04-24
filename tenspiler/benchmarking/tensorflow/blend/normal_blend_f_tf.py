####### import statements ########
import tensorflow as tf


def normal_blend_f_tf(base, active, opacity):
    return ((opacity) * (active)) + (((1) - (opacity)) * (base))


def normal_blend_f_tf_glued(base, active, opacity):
    base = tf.convert_to_tensor(base, dtype=tf.float32)
    active = tf.convert_to_tensor(active, dtype=tf.float32)
    return normal_blend_f_tf(base, active, opacity)


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
        base = bases[i].flatten().astype(np.float32)
        active = actives[i].flatten().astype(np.float32)
        with tf.device("/CPU:0"):
            b = tf.convert_to_tensor(base, np.float32)
            a = tf.convert_to_tensor(active, np.float32)
            opacity = float(rng.random(dtype=np.float32))
        with tf.device("/GPU:0"):
            start_time = time.perf_counter()
            b = tf.identity(b)
            a = tf.identity(a)

            res = normal_blend_f_tf(b, a, opacity)
        with tf.device("/CPU:0"):
            res = tf.identity(res)
            end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("normal_blend_f_tf")
print(f"{np.average(times)} {np.std(times)}")


times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(bases)):
        base = bases[i].flatten().astype(np.float32)
        active = actives[i].flatten().astype(np.float32)
        with tf.device("/GPU:0"):
            b = tf.convert_to_tensor(base, np.float32)
            a = tf.convert_to_tensor(active, np.float32)
            opacity = float(rng.random(dtype=np.float32))
            start_time = time.perf_counter()
            normal_blend_f_tf(b, a, opacity)
            end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print(f"{np.average(times)} {np.std(times)}")
