####### import statements ########
import tensorflow as tf


def rmsnorm_part1_tf(input, weight):
    return tf.reduce_sum((input) * (input))


def rmsnorm_part1_tf_glued(input, weight):
    input = tf.convert_to_tensor(input, dtype=tf.float32)
    weight = tf.convert_to_tensor(weight, dtype=tf.float32)
    return rmsnorm_part1_tf(input, weight)


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

weights = []
w_input = []

with h5py.File(weights_path, "r") as weight_file:
    for layer_name in weight_file:
        w = np.squeeze(np.array(weight_file[layer_name])).astype(np.float32)
        if (
            "model" in layer_name
            and "embed_tokens" not in layer_name
            and "layernorm" not in layer_name
        ):
            weights.append(w)
            w_input.append(rng.random(w.shape, dtype=np.float32))

####### runner. need to manually update for each file ########
runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(weights)):
        input = w_input[i].flatten()
        weight = weights[i].flatten()

        with tf.device("/CPU:0"):
            w = tf.convert_to_tensor(weight, np.float32)
            inp = tf.convert_to_tensor(input, np.float32)
        with tf.device("/GPU:0"):
            start_time = time.perf_counter()
            w = tf.identity(w)
            inp = tf.identity(inp)
            res = rmsnorm_part1_tf(inp, w)
        with tf.device("/CPU:0"):
            res = tf.identity(res)
            end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("rmsnorm_part1_tf")
print(f"{np.average(times)} {np.std(times)}")

times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(weights)):
        input = w_input[i].flatten()
        weight = weights[i].flatten()

        with tf.device("/GPU:0"):
            w = tf.convert_to_tensor(weight, np.float32)
            inp = tf.convert_to_tensor(input, np.float32)
            start_time = time.perf_counter()
            rmsnorm_part1_tf(inp, w)
            end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print(f"{np.average(times)} {np.std(times)}")
