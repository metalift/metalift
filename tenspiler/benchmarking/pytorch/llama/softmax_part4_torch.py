####### import statements ########
import torch


def softmax_part4_torch(unnormalized_output, max_pos, sum):
    return (unnormalized_output[:max_pos]) / (sum)


def softmax_part4_torch_glued(unnormalized_output, max_pos, sum):
    unnormalized_output = torch.tensor(unnormalized_output, dtype=torch.float32)
    return softmax_part4_torch(unnormalized_output, max_pos, sum)


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

attn_weights = []

with h5py.File(weights_path, "r") as weight_file:
    for layer_name in weight_file:
        w = np.squeeze(np.array(weight_file[layer_name])).astype(np.float32)

        if "attn" in layer_name:
            attn_weights.append(w)

####### runner. need to manually update for each file ########
runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(attn_weights)):
        input = attn_weights[i].flatten()
        mp = len(input)
        output = np.exp(input[:mp] - np.max(input[:mp]))
        s = float(np.sum(output[:mp]))

        outp = torch.from_numpy(output).to(dtype=torch.float32).to(cpu)
        max_pos = mp
        sum = s

        start_time = time.perf_counter()
        outp = outp.to(device)
        res = softmax_part4_torch(outp, max_pos, sum)
        res = res.to(cpu)
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("softmax_part4_torch")
print(f"{np.average(times)} {np.std(times)}")

times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(attn_weights)):
        input = attn_weights[i].flatten()
        mp = len(input)
        output = np.exp(input[:mp] - np.max(input[:mp]))
        s = float(np.sum(output[:mp]))

        outp = torch.from_numpy(output).to(dtype=torch.float32).to(device)
        max_pos = mp
        sum = s

        start_time = time.perf_counter()
        softmax_part4_torch(outp, max_pos, sum)
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print(f"{np.average(times)} {np.std(times)}")
