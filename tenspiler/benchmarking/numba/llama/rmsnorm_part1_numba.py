####### import statements ########
import numpy as np
from numba import cuda


@cuda.jit()
def rmsnorm_part1_numba(input, weight, res):
    ss = 0
    for i in range(len(input)):
        ss += input[i] * input[i]
    res[0] = ss
    # return ss


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
inp = w_input[-1].flatten()
w = weights[-1].flatten()
res = np.array([0], dtype=np.float32)

threadsperblock = 32
blockspergrid = (inp.size + (threadsperblock - 1)) // threadsperblock

rmsnorm_part1_numba[blockspergrid, threadsperblock](inp, w, res)

runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(weights)):
        inp = w_input[i].flatten()
        w = weights[i].flatten()
        res = np.array([0], dtype=np.float32)

        threadsperblock = 32
        blockspergrid = (inp.size + (threadsperblock - 1)) // threadsperblock

        start_time = time.perf_counter()
        rmsnorm_part1_numba[blockspergrid, threadsperblock](inp, w, res)
        end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("rmsnorm_part1_nb")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
