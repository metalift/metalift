
####### import statements ########
import mlx.core as mx

def rmsnorm_part1_mx (input, weight):
    return mx.sum((input) * (input))

def rmsnorm_part1_mx_glued (input, weight):
    input = mx.array(input, mx.float32)
    weight = mx.array(weight, mx.float32)
    return rmsnorm_part1_mx(input, weight)


####### more import statements for benchmarking ########
import numpy as np
import time
import h5py

####### setup for benchmarking ########
rng = np.random.default_rng(1)

weights_path = './vicuna_weight7b.h5'

weights = []
w_input = []

#data here are float16 to fit in ram. they are casted to float32 during actual computation
with h5py.File(weights_path, 'r') as weight_file:
    for layer_name in weight_file:
        w = np.squeeze(np.array(weight_file[layer_name])).astype(np.float16)
        if "model" in layer_name and "embed_tokens" not in layer_name and "layernorm" not in layer_name:
            weights.append(w)
            w_input.append(rng.random(w.shape, dtype = np.float32).astype(np.float16))

####### runner. need to manually update for each file ########  
runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(weights)):
        input = w_input[i].flatten().astype(np.float32)
        weight = weights[i].flatten().astype(np.float32)

               
        inp = mx.array(input, mx.float32)
        w = mx.array(weight, mx.float32)

        start_time = time.perf_counter()
        mx.eval(rmsnorm_part1_mx(inp, w))
        end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)   

print("rmsnorm_part1_mx")
print(f"{np.average(times)} {np.std(times)}") 
print(f"{np.average(times)} {np.std(times)}") 
