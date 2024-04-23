####### import statements ########
import mlx.core as mx


def softmax_part3_mx(output, max_pos):
    return mx.sum(output[:max_pos])


def softmax_part3_mx_glued(output, max_pos):
    output = mx.array(output, mx.float32)
    return softmax_part3_mx(output, max_pos)


import time

import h5py

####### more import statements for benchmarking ########
import numpy as np

####### setup for benchmarking ########
rng = np.random.default_rng(1)

weights_path = "./tenspiler/data/vicuna_weight7b.h5"


attn_weights = []
# data here are float16 to fit in ram. they are casted to float32 during actual computation
with h5py.File(weights_path, "r") as weight_file:
    for layer_name in weight_file:
        w = np.squeeze(np.array(weight_file[layer_name])).astype(np.float16)
        if "attn" in layer_name:
            attn_weights.append(w)

####### runner. need to manually update for each file ########
runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(attn_weights)):
        input = attn_weights[i].flatten().astype(np.float32)
        mp = len(input)
        output = np.exp(input[:mp] - np.max(input[:mp]))

        outp = mx.array(output, mx.float32)
        max_pos = mp

        start_time = time.perf_counter()
        mx.eval(softmax_part3_mx(outp, max_pos))
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("softmax_part3_mx")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
