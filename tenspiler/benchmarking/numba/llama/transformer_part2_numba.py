####### import statements ########
import numpy as np
from numba import cuda


@cuda.jit()
def transformer_part2_numba(
    token_position, head, head_size, key_cache_layer, attention, res
):
    # xb = []
    for i in range(head_size):
        curr = 0
        for timestep in range(token_position):
            curr += (
                attention[timestep] * key_cache_layer[timestep][head * head_size + i]
            )
        # xb.append(curr)
        res[i] = curr
    # return xb


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


def transformer_part1_numba(token_position, head, head_size, key_cache_layer, q):
    return (
        np.matmul(
            key_cache_layer[:token_position][
                :, (head) * (head_size) : (head) * (head_size) + head_size
            ],
            q[(head) * (head_size) : (head) * (head_size) + head_size],
        )
    ) / (np.sqrt((head_size) * (1)))


####### runner. need to manually update for each file ########
k_matrix = k_weights[-1]
q_matrix = q_weights[-1]
token_position = k_matrix.shape[0] - 1

num_head = 32
head = rng.integers(low=0, high=num_head)
head_size = k_matrix.shape[0] // num_head

key_cache_layer = k_matrix
q = q_matrix.flatten()

attention = transformer_part1_numba(token_position, head, head_size, key_cache_layer, q)
attention = np.append(attention, np.array([0]))

threadsperblock = 32
blockspergrid = (k_matrix.size + (threadsperblock - 1)) // threadsperblock

res = np.array([0 for _ in range(head_size)], dtype=np.float32)

transformer_part2_numba[blockspergrid, threadsperblock](
    token_position, head, head_size, key_cache_layer, attention, res
)

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

        attention = transformer_part1_numba(
            token_position, head, head_size, key_cache_layer, q
        )
        attention = np.append(attention, np.array([0]))

        threadsperblock = 32
        blockspergrid = (k_matrix.size + (threadsperblock - 1)) // threadsperblock

        res = np.array([0 for _ in range(head_size)], dtype=np.float32)

        start_time = time.perf_counter()
        transformer_part2_numba[blockspergrid, threadsperblock](
            token_position, head, head_size, key_cache_layer, attention, res
        )
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("transformer_part2_numba")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
