
####### import statements ########
import numpy as np

def softmax_part2_np (input, max_pos, max_val):
    return np.exp((input[:max_pos]) - (max_val))

def softmax_part2_np_glued (input, max_pos, max_val):
    input = np.array(input).astype(np.float32)
    return softmax_part2_np(input, max_pos, max_val)


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
runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(attn_weights)):
        inp = attn_weights[i].flatten()
        max_pos = len(inp)
        
        max_val = float(np.max(inp[:max_pos]))

        start_time = time.perf_counter()
        softmax_part2_np(inp, max_pos, max_val)
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)   

print("softmax_part2_np")
print(f"{np.average(times)} {np.std(times)}") 
print(f"{np.average(times)} {np.std(times)}") 
