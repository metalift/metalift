
####### import statements ########
import numpy as np
from numba import jit, cuda

@jit(nopython=True)
def softmax_part4_numba_jit (unnormalized_output, max_pos, sum):
    # output = []
    output = np.empty(max_pos)
    for i in range(max_pos):
        output[i] = unnormalized_output[i] / sum
        # output.append(unnormalized_output[i] / sum)
    return output

####### more import statements for benchmarking ########
import time
import h5py

####### setup for benchmarking ########
rng = np.random.default_rng(1)

weights_path = './vicuna_weight.h5'

attn_weights = []


with h5py.File(weights_path, 'r') as weight_file:
    for layer_name in weight_file:
        w = np.squeeze(np.array(weight_file[layer_name])).astype(np.float32)
        
        if "attn" in layer_name:
            attn_weights.append(w)
            
####### runner. need to manually update for each file ########  

inp = attn_weights[-1].flatten()
max_pos = len(inp)
outp = np.exp(inp[:max_pos]-np.max(inp[:max_pos]))
sum = float(np.sum(outp[:max_pos]))



softmax_part4_numba_jit(outp, max_pos, sum)

runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(attn_weights)):
        inp = attn_weights[i].flatten()
        max_pos = len(inp)
        outp = np.exp(inp[:max_pos]-np.max(inp[:max_pos]))
        sum = float(np.sum(outp[:max_pos]))
        
        

        start_time = time.perf_counter()
        softmax_part4_numba_jit(outp, max_pos, sum)
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)   

print("softmax_part4_numba_jit")
print(f"{np.average(times)} {np.std(times)}") 
print(f"{np.average(times)} {np.std(times)}") 
