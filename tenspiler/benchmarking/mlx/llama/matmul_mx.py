####### import statements ########
import mlx.core as mx


def matmul_mx(weight, input):
    return mx.matmul(weight, input)


def matmul_mx_glued(weight, input):
    weight = mx.array(weight, mx.float32)
    input = mx.array(input, mx.float32)
    return matmul_mx(weight, input)


import time

import h5py

####### more import statements for benchmarking ########
import numpy as np

####### setup for benchmarking ########
rng = np.random.default_rng(1)

weights_path = "./tenspiler/data/vicuna_weight7b.h5"

attn_weights = []
aw_input = []

# data here are float16 to fit in ram. they are casted to float32 during actual computation
with h5py.File(weights_path, "r") as weight_file:
    for layer_name in weight_file:
        w = np.squeeze(np.array(weight_file[layer_name])).astype(np.float16)
        if "attn" in layer_name:
            attn_weights.append(w)
            aw_input.append(rng.random(w.shape[1], dtype=np.float32).astype(np.float16))

####### runner. need to manually update for each file ########
runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(aw_input)):
        weight = attn_weights[i].astype(np.float32)
        input = aw_input[i].astype(np.float32)

        w = mx.array(weight, mx.float32)
        inp = mx.array(input, mx.float32)

        start_time = time.perf_counter()
        mx.eval(matmul_mx(w, inp))
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("matmul_mx")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
