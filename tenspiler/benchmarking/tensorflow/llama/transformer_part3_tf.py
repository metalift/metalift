####### import statements ########
import tensorflow as tf


def transformer_part3_tf(input, hidden_dim):
    return (input[:hidden_dim]) * ((1) / ((1) + (tf.exp((0) - (input[:hidden_dim])))))


def transformer_part3_tf_glued(input, hidden_dim):
    input = tf.convert_to_tensor(input, dtype=tf.float32)
    return transformer_part3_tf(input, hidden_dim)


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

with h5py.File(weights_path, "r") as weight_file:
    for layer_name in weight_file:
        w = np.squeeze(np.array(weight_file[layer_name])).astype(np.float32)
        if (
            "model" in layer_name
            and "embed_tokens" not in layer_name
            and "layernorm" not in layer_name
        ):
            weights.append(w)

####### runner. need to manually update for each file ########
runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(weights)):
        input = weights[i].flatten()
        hd = len(input)

        with tf.device("/CPU:0"):
            inp = tf.convert_to_tensor(input, np.float32)
            hidden_dim = hd
        with tf.device("/GPU:0"):
            start_time = time.perf_counter()
            inp = tf.identity(inp)

            res = transformer_part3_tf(inp, hidden_dim)
        with tf.device("/CPU:0"):
            res = tf.identity(res)
            end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("transformer_part3_tf")
print(f"{np.average(times)} {np.std(times)}")

times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(weights)):
        input = weights[i].flatten()
        hd = len(input)

        with tf.device("/GPU:0"):
            inp = tf.convert_to_tensor(input, np.float32)
            hidden_dim = hd
            start_time = time.perf_counter()
            transformer_part3_tf(inp, hidden_dim)
            end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print(f"{np.average(times)} {np.std(times)}")
