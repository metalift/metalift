####### import statements ########
import torch


def transformer_part1_torch(token_position, head, head_size, key_cache_layer, q):
    return (
        torch.matmul(
            key_cache_layer[0:token_position][
                :, (head) * (head_size) : (head) * (head_size) + head_size
            ],
            q[(head) * (head_size) : (head) * (head_size) + head_size],
        )
    ) / (torch.sqrt(torch.as_tensor((head_size) * (1))))


def transformer_part1_torch_glued(token_position, head, head_size, key_cache_layer, q):
    key_cache_layer = torch.tensor(key_cache_layer, dtype=torch.float32)
    q = torch.tensor(q, dtype=torch.float32)
    return transformer_part1_torch(token_position, head, head_size, key_cache_layer, q)


import time

import h5py

####### more import statements for benchmarking ########
import numpy as np

####### setup for benchmarking ########
rng = np.random.default_rng(1)
if not torch.cuda.is_available():
    print("CUDA is not available on this system")
device = "cuda" if torch.cuda.is_available() else "cpu"
cpu = "cpu"

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

        key_cache_layer = torch.from_numpy(k_matrix).to(cpu)
        q = torch.from_numpy(q_matrix.flatten()).to(cpu)

        start_time = time.perf_counter()
        key_cache_layer = key_cache_layer.to(device)
        q = q.to(device)
        res = transformer_part1_torch(
            token_position, head, head_size, key_cache_layer, q
        )
        res = res.to(cpu)
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("transformer_part1_torch")
print(f"{np.average(times)} {np.std(times)}")

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

        key_cache_layer = torch.from_numpy(k_matrix).to(device)
        q = torch.from_numpy(q_matrix.flatten()).to(device)

        start_time = time.perf_counter()
        transformer_part1_torch(token_position, head, head_size, key_cache_layer, q)
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print(f"{np.average(times)} {np.std(times)}")
