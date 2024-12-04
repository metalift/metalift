####### import statements ########
import torch


def transformer_part3_torch(input, hidden_dim):
    return (input[:hidden_dim]) * (
        (1) / ((1) + (torch.exp(torch.as_tensor((0) - (input[:hidden_dim])))))
    )


def transformer_part3_torch_glued(input, hidden_dim):
    input = torch.tensor(input, dtype=torch.float32)
    return transformer_part3_torch(input, hidden_dim)


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
        input = weights[i].flatten()
        hd = len(input)

        inp = torch.from_numpy(input).to(dtype=torch.float32).to(cpu)
        hidden_dim = hd

        start_time = time.perf_counter()
        inp = inp.to(device)

        res = transformer_part3_torch(inp, hidden_dim)
        res = res.to(cpu)
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("transformer_part3_torch")
print(f"{np.average(times)} {np.std(times)}")

times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(weights)):
        input = weights[i].flatten()
        hd = len(input)

        inp = torch.from_numpy(input).to(dtype=torch.float32).to(device)
        hidden_dim = hd
        start_time = time.perf_counter()
        transformer_part3_torch(inp, hidden_dim)
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print(f"{np.average(times)} {np.std(times)}")
