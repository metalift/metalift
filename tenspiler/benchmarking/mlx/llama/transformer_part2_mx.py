####### import statements ########
import mlx.core as mx


def transformer_part2_mx(token_position, head, head_size, key_cache_layer, attention):
    return mx.matmul(
        mx.transpose(
            key_cache_layer[0 : (token_position) + (1)][
                :, (head) * (head_size) : (head) * (head_size) + head_size
            ]
        ),
        attention[: (token_position) + (1)],
    )


def transformer_part2_mx_glued(
    token_position, head, head_size, key_cache_layer, attention
):
    key_cache_layer = mx.array(key_cache_layer, mx.float32)
    attention = mx.array(attention, mx.float32)
    return transformer_part2_mx(
        token_position, head, head_size, key_cache_layer, attention
    )


import time

import h5py

####### more import statements for benchmarking ########
import numpy as np

####### setup for benchmarking ########
rng = np.random.default_rng(1)

weights_path = "./vicuna_weight7b.h5"

q_weights = []
k_weights = []
# data here are float16 to fit in ram. they are casted to float32 during actual computation
with h5py.File(weights_path, "r") as weight_file:
    for layer_name in weight_file:
        w = np.squeeze(np.array(weight_file[layer_name])).astype(np.float16)

        if "attn" in layer_name:
            if "q_proj" in layer_name:
                q_weights.append(w)
            if "k_proj" in layer_name:
                k_weights.append(w)


def transformer_part1_mx(token_position, head, head_size, key_cache_layer, q):
    return (
        mx.matmul(
            key_cache_layer[:token_position][
                :, (head) * (head_size) : (head) * (head_size) + head_size
            ],
            q[(head) * (head_size) : (head) * (head_size) + head_size],
        )
    ) / (mx.sqrt(mx.array((head_size) * (1))))


####### runner. need to manually update for each file ########
runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(q_weights)):
        k_matrix = k_weights[i].astype(np.float32)
        q_matrix = q_weights[i].astype(np.float32)
        token_position = k_matrix.shape[0] - 1

        num_head = 32
        head = int(rng.integers(low=0, high=num_head))
        head_size = k_matrix.shape[0] // num_head

        key_cache_layer = mx.array(k_matrix, mx.float32)
        q = mx.array(q_matrix.flatten(), mx.float32)

        attention = transformer_part1_mx(
            token_position, head, head_size, key_cache_layer, q
        )
        attention = mx.concatenate([attention, mx.array([0])])

        start_time = time.perf_counter()
        mx.eval(
            transformer_part2_mx(
                token_position, head, head_size, key_cache_layer, attention
            )
        )
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("transformer_part2_mx")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
