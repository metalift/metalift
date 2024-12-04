####### import statements ########
import torch


def matmul_torch(weight, input):
    return torch.matmul(weight, input)


def matmul_torch_glued(weight, input):
    weight = torch.tensor(weight, dtype=torch.float32)
    input = torch.tensor(input, dtype=torch.float32)
    return matmul_torch(weight, input)


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
        weight = attn_weights[i]
        input = aw_input[i]

        w = torch.from_numpy(weight).to(dtype=torch.float32).to(cpu)
        inp = torch.from_numpy(input).to(dtype=torch.float32).to(cpu)

        start_time = time.perf_counter()
        w = w.to(device)
        inp = inp.to(device)
        res = matmul_torch(w, inp)
        res = res.to(cpu)
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("matmul_torch")
print(f"{np.average(times)} {np.std(times)}")

times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(attn_weights)):
        weight = attn_weights[i]
        input = aw_input[i]

        w = torch.from_numpy(weight).to(dtype=torch.float32).to(device)
        inp = torch.from_numpy(input).to(dtype=torch.float32).to(device)

        start_time = time.perf_counter()
        matmul_torch(w, inp)
        end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print(f"{np.average(times)} {np.std(times)}")
