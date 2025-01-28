####### import statements ########
import math

import numpy as np
from numba import cuda


@cuda.jit()
def transformer_part1_numba(token_position, head, head_size, key_cache_layer, q, res):
    # attention = []
    for timestep in range(token_position):
        score = 0
        for i in range(head_size):
            score += (
                q[head * head_size + i]
                * key_cache_layer[timestep][head * head_size + i]
            )
        score /= math.sqrt(head_size * 1)
        # attention.append(score)
        res[timestep] = score
    # return attention


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
k_matrix = k_weights[-1]
q_matrix = q_weights[-1]
token_position = k_matrix.shape[0] - 1

res = np.array([0 for _ in range(token_position)], dtype=np.float32)

num_head = 32
head = rng.integers(low=0, high=num_head)
head_size = k_matrix.shape[0] // num_head

key_cache_layer = k_matrix
q = q_matrix.flatten()

threadsperblock = 32
blockspergrid = (k_matrix.size + (threadsperblock - 1)) // threadsperblock

transformer_part1_numba[blockspergrid, threadsperblock](
    token_position, head, head_size, key_cache_layer, q, res
)


runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(q_weights)):
        k_matrix = k_weights[i]
        q_matrix = q_weights[i]
        token_position = k_matrix.shape[0] - 1
        res = np.array([0 for _ in range(token_position)], dtype=np.float32)

        num_head = 32
        head = rng.integers(low=0, high=num_head)
        head_size = k_matrix.shape[0] // num_head

        key_cache_layer = k_matrix
        q = q_matrix.flatten()

        threadsperblock = 32
        blockspergrid = (k_matrix.size + (threadsperblock - 1)) // threadsperblock

        start_time = time.perf_counter()
        transformer_part1_numba[blockspergrid, threadsperblock](
            token_position, head, head_size, key_cache_layer, q, res
        )
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("transformer_part1_numba")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
