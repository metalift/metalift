####### import statements ########
import numpy as np


def rmsnorm_part1_np(input, weight):
    return np.sum((input) * (input))


def rmsnorm_part1_np_glued(input, weight):
    input = np.array(input).astype(np.float32)
    weight = np.array(weight).astype(np.float32)
    return rmsnorm_part1_np(input, weight)


####### more import statements for benchmarking ########
import time

import h5py

####### setup for benchmarking ########
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
        inp = w_input[i].flatten()
        w = weights[i].flatten()

        start_time = time.perf_counter()
        rmsnorm_part1_np(inp, w)
        end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("rmsnorm_part1_np")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
