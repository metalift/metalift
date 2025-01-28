####### import statements ########
import tensorflow as tf


def softmax_part2_tf(input, max_pos, max_val):
    return tf.exp((input[:max_pos]) - (max_val))


def softmax_part2_tf_glued(input, max_pos, max_val):
    input = tf.convert_to_tensor(input, dtype=tf.float32)
    return softmax_part2_tf(input, max_pos, max_val)


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

with h5py.File(weights_path, "r") as weight_file:
    for layer_name in weight_file:
        w = np.squeeze(np.array(weight_file[layer_name])).astype(np.float32)

        if "attn" in layer_name:
            attn_weights.append(w)

####### runner. need to manually update for each file ########
runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(attn_weights)):
        input = attn_weights[i].flatten()
        mp = len(input)

        with tf.device("/CPU:0"):
            inp = tf.convert_to_tensor(input, np.float32)
            max_pos = mp
            max_val = float(np.max(input[:mp]))
        with tf.device("/GPU:0"):
            start_time = time.perf_counter()
            inp = tf.identity(inp)

            res = softmax_part2_tf(inp, max_pos, max_val)
        with tf.device("/CPU:0"):
            res = tf.identity(res)
            end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("softmax_part2_tf")
print(f"{np.average(times)} {np.std(times)}")

times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(attn_weights)):
        input = attn_weights[i].flatten()
        mp = len(input)

        with tf.device("/GPU:0"):
            inp = tf.convert_to_tensor(input, np.float32)
            max_pos = mp
            max_val = np.max(input[:mp])

            start_time = time.perf_counter()
            softmax_part2_tf(inp, max_pos, max_val)
            end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print(f"{np.average(times)} {np.std(times)}")
