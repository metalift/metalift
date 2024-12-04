####### import statements ########
import numpy as np


def transformer_part1_np(token_position, head, head_size, key_cache_layer, q):
    return (
        np.matmul(
            key_cache_layer[0:token_position][
                :, (head) * (head_size) : (head) * (head_size) + head_size
            ],
            q[(head) * (head_size) : (head) * (head_size) + head_size],
        )
    ) / (np.sqrt((head_size) * (1)))


def transformer_part1_np_glued(token_position, head, head_size, key_cache_layer, q):
    key_cache_layer = np.array(key_cache_layer).astype(np.float32)
    q = np.array(q).astype(np.float32)
    return transformer_part1_np(token_position, head, head_size, key_cache_layer, q)


import time

import h5py

####### more import statements for benchmarking ########
import numpy as np

####### setup for benchmarking ########
rng = np.random.default_rng(1)

weights_path = "./vicuna_weight.h5"

q_weights = []
k_weights = []

with h5py.File(weights_path, "r") as weight_file:
    for layer_name in weight_file:
        w = np.squeeze(np.array(weight_file[layer_name])).astype(np.float32)
        if "attn" in layer_name:
            if "q_proj" in layer_name:
                q_weights.append(w)
            if "k_proj" in layer_name:
                k_weights.append(w)

####### runner. need to manually update for each file ########
runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(q_weights)):
        k_matrix = k_weights[i]
        q_matrix = q_weights[i]
        token_position = k_matrix.shape[0] - 1

        num_head = 32
        head = rng.integers(low=0, high=num_head)
        head_size = k_matrix.shape[0] // num_head

        key_cache_layer = k_matrix
        q = q_matrix.flatten()

        start_time = time.perf_counter()
        transformer_part1_np(token_position, head, head_size, key_cache_layer, q)
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("transformer_part1_np")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
