####### import statements ########
import math

import numpy as np
from numba import cuda


@cuda.jit()
def softmax_part2_numba(input, max_pos, max_val, res):
    # output = []
    for i in range(max_pos):
        res[i] = math.exp(input[i] - max_val)
        # output.append(cur)
    # return output


####### more import statements for benchmarking ########
import time

import h5py

####### setup for benchmarking ########
rng = np.random.default_rng(1)

weights_path = "./vicuna_weight.h5"

attn_weights = []


with h5py.File(weights_path, "r") as weight_file:
    for layer_name in weight_file:
        w = np.squeeze(np.array(weight_file[layer_name])).astype(np.float32)

        if "attn" in layer_name:
            attn_weights.append(w)

####### runner. need to manually update for each file ########

inp = attn_weights[-1].flatten()
res = np.empty(inp.shape, dtype=np.float32)
max_pos = len(inp)

max_val = float(np.max(inp[:max_pos]))

threadsperblock = 32
blockspergrid = (inp.size + (threadsperblock - 1)) // threadsperblock

softmax_part2_numba[blockspergrid, threadsperblock](inp, max_pos, max_val, res)

runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(attn_weights)):
        inp = attn_weights[i].flatten()
        res = np.empty(inp.shape, dtype=np.float32)
        max_pos = len(inp)

        max_val = float(np.max(inp[:max_pos]))

        threadsperblock = 32
        blockspergrid = (inp.size + (threadsperblock - 1)) // threadsperblock

        start_time = time.perf_counter()
        softmax_part2_numba[blockspergrid, threadsperblock](inp, max_pos, max_val, res)
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("softmax_part2_numba")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
