####### import statements ########
import torch


def transformer_part4_torch(input1, input2, hidden_dim):
    return (input1[:hidden_dim]) * (input2[:hidden_dim])


def transformer_part4_torch_glued(input1, input2, hidden_dim):
    input1 = torch.tensor(input1, dtype=torch.float32)
    input2 = torch.tensor(input2, dtype=torch.float32)
    return transformer_part4_torch(input1, input2, hidden_dim)


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
        input1 = weights[i].flatten()
        input2 = w_input[i].flatten()
        hd = len(input1)

        inp1 = torch.from_numpy(input1).to(dtype=torch.float32).to(cpu)
        inp2 = torch.from_numpy(input2).to(dtype=torch.float32).to(cpu)
        hidden_dim = hd

        start_time = time.perf_counter()
        inp1 = inp1.to(device)
        inp2 = inp2.to(device)

        res = transformer_part4_torch(inp1, inp2, hidden_dim)
        res = res.to(cpu)
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("transformer_part4_torch")
print(f"{np.average(times)} {np.std(times)}")

times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(weights)):
        input1 = weights[i].flatten()
        input2 = w_input[i].flatten()
        hd = len(input1)

        inp1 = torch.from_numpy(input1).to(dtype=torch.float32).to(device)
        inp2 = torch.from_numpy(input2).to(dtype=torch.float32).to(device)
        hidden_dim = hd

        start_time = time.perf_counter()
        transformer_part4_torch(inp1, inp2, hidden_dim)
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print(f"{np.average(times)} {np.std(times)}")
