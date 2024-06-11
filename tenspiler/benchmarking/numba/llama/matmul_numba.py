
####### import statements ########
import numpy as np
from numba import jit, cuda

@cuda.jit()
def matmul_numba (weight, input):
    # output = []
    m = len(weight)
    n = len(input)
    for i in range(m):
        curr = 0
        for j in range(n):
            curr += weight[i][j] * input[j]
        # output.append(curr)
    # return output

####### more import statements for benchmarking ########
import time
import h5py

####### setup for benchmarking ########
rng = np.random.default_rng(1)

weights_path = './vicuna_weight.h5'

attn_weights = []
aw_input = []


with h5py.File(weights_path, 'r') as weight_file:
    for layer_name in weight_file:
        w = np.squeeze(np.array(weight_file[layer_name])).astype(np.float32)
        if "attn" in layer_name:
            attn_weights.append(w)
            aw_input.append(rng.random(w.shape[1], dtype = np.float32))

####### runner. need to manually update for each file ########  
w = attn_weights[-1]
inp = aw_input[-1]

threadsperblock = 32
blockspergrid = (w.size + (threadsperblock - 1)) // threadsperblock

matmul_numba[blockspergrid, threadsperblock](w, inp)

runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(attn_weights)):
        w = attn_weights[i]
        inp = aw_input[i]

        threadsperblock = 32
        blockspergrid = (w.size + (threadsperblock - 1)) // threadsperblock

        start_time = time.perf_counter()
        matmul_numba[blockspergrid, threadsperblock](w, inp)
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000


    times.append(total_time)

times = np.array(times)   

print("matmul_numba")
print(f"{np.average(times)} {np.std(times)}") 
print(f"{np.average(times)} {np.std(times)}") 