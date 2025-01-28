####### import statements ########
import tensorflow as tf


def matmul_tf(weight, input):
    return tf.linalg.matvec(weight, input)


def matmul_tf_glued(weight, input):
    weight = tf.convert_to_tensor(weight, dtype=tf.float32)
    input = tf.convert_to_tensor(input, dtype=tf.float32)
    return matmul_tf(weight, input)


import time

import h5py

####### more import statements for benchmarking ########
import numpy as np

####### setup for benchmarking ########
gpus = tf.config.list_physical_devices("GPU")
if not gpus:
    print("No GPU is available")
rng = np.random.default_rng(1)

weights_path = "./vicuna_weight.h5"

attn_weights = []
aw_input = []

with h5py.File(weights_path, "r") as weight_file:
    for layer_name in weight_file:
        w = np.squeeze(np.array(weight_file[layer_name])).astype(np.float32)
        if "attn" in layer_name:
            attn_weights.append(w)
            aw_input.append(rng.random(w.shape[1], dtype=np.float32))

####### runner. need to manually update for each file ########
runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(attn_weights)):
        weight = attn_weights[i]
        input = aw_input[i]

        with tf.device("/CPU:0"):
            w = tf.convert_to_tensor(weight, np.float32)
            inp = tf.convert_to_tensor(input, np.float32)
        with tf.device("/GPU:0"):
            start_time = time.perf_counter()
            w = tf.identity(w)
            inp = tf.identity(inp)
            res = matmul_tf(w, inp)
        with tf.device("/CPU:0"):
            res = tf.identity(res)
            end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("matmul_tf")
print(f"{np.average(times)} {np.std(times)}")

times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(attn_weights)):
        weight = attn_weights[i]
        input = aw_input[i]

        with tf.device("/GPU:0"):
            w = tf.convert_to_tensor(weight, np.float32)
            inp = tf.convert_to_tensor(input, np.float32)

            start_time = time.perf_counter()
            matmul_tf(w, inp)
            end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print(f"{np.average(times)} {np.std(times)}")
