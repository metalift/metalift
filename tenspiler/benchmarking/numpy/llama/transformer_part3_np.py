####### import statements ########
import numpy as np


def transformer_part3_np(input, hidden_dim):
    return (input[:hidden_dim]) * ((1) / ((1) + (np.exp((0) - (input[:hidden_dim])))))


def transformer_part3_np_glued(input, hidden_dim):
    input = np.array(input).astype(np.float32)
    return transformer_part3_np(input, hidden_dim)


import time

import h5py

####### more import statements for benchmarking ########
import numpy as np

####### setup for benchmarking ########
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
        inp = weights[i].flatten()
        hidden_dim = len(inp)

        start_time = time.perf_counter()
        transformer_part3_np(inp, hidden_dim)
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("transformer_part3_np")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
