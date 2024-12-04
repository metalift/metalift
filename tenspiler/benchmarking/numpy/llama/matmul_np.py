####### import statements ########
import numpy as np


def matmul_np(weight, input):
    return np.matmul(weight, input)


def matmul_np_glued(weight, input):
    weight = np.array(weight).astype(np.float32)
    input = np.array(input).astype(np.float32)
    return matmul_np(weight, input)


####### more import statements for benchmarking ########
import time

import h5py

####### setup for benchmarking ########
rng = np.random.default_rng(1)

weights_path = "./vicuna_weight.h5"

attn_weights = []
aw_input = []


with h5py.File(weights_path, "r") as weight_file:
    for layer_name in weight_file:
        w = np.squeeze(np.array(weight_file[layer_name])).astype(np.float32)
        if "attn" in layer_name:
            attn_weights.append(w)
            aw_input.append(rng.random(w.shape[1], dtype=np.float32))

####### runner. need to manually update for each file ########
runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(attn_weights)):
        w = attn_weights[i]
        inp = aw_input[i]

        start_time = time.perf_counter()
        matmul_np(w, inp)
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("matmul_np")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
