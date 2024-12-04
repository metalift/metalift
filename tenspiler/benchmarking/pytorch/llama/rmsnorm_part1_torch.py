####### import statements ########
import torch


def rmsnorm_part1_torch(input, weight):
    return torch.sum((input) * (input))


def rmsnorm_part1_torch_glued(input, weight):
    input = torch.tensor(input, dtype=torch.float32)
    weight = torch.tensor(weight, dtype=torch.float32)
    return rmsnorm_part1_torch(input, weight)


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
        input = w_input[i].flatten()
        weight = weights[i].flatten()

        inp = torch.from_numpy(input).to(dtype=torch.float32).to(cpu)
        w = torch.from_numpy(weight).to(dtype=torch.float32).to(cpu)

        start_time = time.perf_counter()
        inp = inp.to(device)
        w = w.to(device)
        res = rmsnorm_part1_torch(inp, w)
        res = res.to(cpu)
        end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("rmsnorm_part1_torch")
print(f"{np.average(times)} {np.std(times)}")

times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(weights)):
        input = w_input[i].flatten()
        weight = weights[i].flatten()

        inp = torch.from_numpy(input).to(dtype=torch.float32).to(device)
        w = torch.from_numpy(weight).to(dtype=torch.float32).to(device)
        start_time = time.perf_counter()
        rmsnorm_part1_torch(inp, w)
        end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print(f"{np.average(times)} {np.std(times)}")
