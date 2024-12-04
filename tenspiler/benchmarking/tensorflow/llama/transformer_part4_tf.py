####### import statements ########
import tensorflow as tf


def transformer_part4_tf(input1, input2, hidden_dim):
    return (input1[:hidden_dim]) * (input2[:hidden_dim])


def transformer_part4_tf_glued(input1, input2, hidden_dim):
    input1 = tf.convert_to_tensor(input1, dtype=tf.float32)
    input2 = tf.convert_to_tensor(input2, dtype=tf.float32)
    return transformer_part4_tf(input1, input2, hidden_dim)


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
        input1 = weights[i].flatten()
        input2 = w_input[i].flatten()
        hd = len(input1)

        with tf.device("/CPU:0"):
            inp1 = tf.convert_to_tensor(input1, np.float32)
            inp2 = tf.convert_to_tensor(input2, np.float32)

        with tf.device("/GPU:0"):
            start_time = time.perf_counter()
            inp1 = tf.identity(inp1)
            inp2 = tf.identity(inp2)

            res = transformer_part4_tf(inp1, inp2, hd)
        with tf.device("/CPU:0"):
            res = tf.identity(res)
            end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("transformer_part4_tf")
print(f"{np.average(times)} {np.std(times)}")

times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(weights)):
        input1 = weights[i].flatten()
        input2 = w_input[i].flatten()
        hd = len(input1)

        with tf.device("/GPU:0"):
            inp1 = tf.convert_to_tensor(input1, np.float32)
            inp2 = tf.convert_to_tensor(input2, np.float32)
            hidden_dim = hd

            start_time = time.perf_counter()
            transformer_part4_tf(inp1, inp2, hidden_dim)
            end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print(f"{np.average(times)} {np.std(times)}")
