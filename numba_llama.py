#!/usr/bin/env python
# coding: utf-8

# In[2]:


import math
import time

import h5py
import numpy as np
from numba import njit

# In[3]:


rng = np.random.default_rng(1)


# In[4]:


weights_path = "/tier2/ucb/metalift/vicuna_weight.h5"

weights = []
w_input = []
attn_weights = []
aw_input = []
q_weights = []
k_weights = []

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
        if "attn" in layer_name:
            attn_weights.append(w)
            aw_input.append(rng.random(w.shape[1], dtype=np.float32))
            if "q_proj" in layer_name:
                q_weights.append(w)
            if "k_proj" in layer_name:
                k_weights.append(w)


# In[5]:


def timer(input1, input2, f, runner):
    runs = 10
    times = []
    start_time = time.perf_counter()
    for _ in range(runs):
        times.append(runner(input1, input2, f))
        curr_time = time.perf_counter()
        if (curr_time - start_time) / 3600 > 2:  # testing has taken more than 2 hr
            print(
                f"Testing has taken more than 2hr for {runner.__name__[:-6]}nb. {len(times)} runs has finished."
            )
            break
    times = np.array(times)
    print(f"{runner.__name__[:-6]}nb")
    print(f"{np.average(times)}ms +/- {np.std(times)}ms")


# In[6]:


@njit
def elewise_mul_nb(input1, input2, hidden_dim):
    output = []
    for i in range(hidden_dim):
        output.append(input1[i] * input2[i])
    return output


def elewise_mul_runner(inputs1, inputs2, f=None):
    total_time = 0
    for i in range(len(inputs1)):
        inp1 = inputs1[i].flatten()
        inp2 = inputs2[i].flatten()
        hidden_dim = len(inp1)

        elewise_mul_nb(inp1, inp2, hidden_dim)
        start_time = time.perf_counter()
        elewise_mul_nb(inp1, inp2, hidden_dim)
        end_time = time.perf_counter()
        del inp2
        del inp1
        total_time += (end_time - start_time) * 1000
    return total_time


# In[7]:


@njit
def matmul_nb(weight, input):
    output = []
    m = len(weight)
    n = len(input)
    for i in range(m):
        curr = 0
        for j in range(n):
            curr += weight[i][j] * input[j]
        output.append(curr)
    return output


def matmul_runner(weights, inputs, f=None):
    total_time = 0
    for i in range(len(inputs)):
        w = weights[i]
        inp = inputs[i]

        matmul_nb(w, inp)
        start_time = time.perf_counter()
        matmul_nb(w, inp)
        end_time = time.perf_counter()
        del inp
        del w
        total_time += (end_time - start_time) * 1000
    return total_time


# In[8]:


@njit
def multiquery_attention_part1_nb(token_position, head, head_size, key_cache_layer, q):
    attention = []
    for timestep in range(token_position):
        score = 0
        for i in range(head_size):
            score += (
                q[head * head_size + i]
                * key_cache_layer[timestep][head * head_size + i]
            )
        score /= math.sqrt(head_size * 1)
        attention.append(score)
    return attention


def multiquery_attention_part1_runner(k_matrixes, q_matrixes, f=None):
    total_time = 0
    for i in range(len(k_matrixes)):
        k_matrix = k_matrixes[i]
        q_matrix = q_matrixes[i]
        token_position = k_matrix.shape[0] - 1

        num_head = 32
        head = int(rng.integers(low=0, high=num_head))
        head_size = k_matrix.shape[0] // num_head

        key_cache_layer = k_matrix
        q = q_matrix.flatten()

        multiquery_attention_part1_nb(
            token_position, head, head_size, key_cache_layer, q
        )
        start_time = time.perf_counter()
        multiquery_attention_part1_nb(
            token_position, head, head_size, key_cache_layer, q
        )
        end_time = time.perf_counter()
        del key_cache_layer
        del q
        total_time += (end_time - start_time) * 1000
    return total_time


# In[9]:


@njit
def multiquery_attention_part2_nb(
    token_position, head, head_size, key_cache_layer, attention
):
    xb = []
    for i in range(head_size):
        curr = 0
        for timestep in range(token_position):
            curr += (
                attention[timestep] * key_cache_layer[timestep][head * head_size + i]
            )
        xb.append(curr)
    return xb


def multiquery_attention_part2_runner(k_matrixes, q_matrixes, f=None):
    total_time = 0
    for i in range(len(k_matrixes)):
        k_matrix = k_matrixes[i]
        q_matrix = q_matrixes[i]
        token_position = k_matrix.shape[0] - 1

        num_head = 32
        head = int(rng.integers(low=0, high=num_head))
        head_size = k_matrix.shape[0] // num_head

        key_cache_layer = k_matrix
        q = q_matrix.flatten()

        attention = np.array(
            multiquery_attention_part1_nb(
                token_position, head, head_size, key_cache_layer, q
            )
        )
        attention = np.append(attention, np.array([0]))

        multiquery_attention_part2_nb(
            token_position, head, head_size, key_cache_layer, attention
        )
        start_time = time.perf_counter()
        multiquery_attention_part2_nb(
            token_position, head, head_size, key_cache_layer, attention
        )
        end_time = time.perf_counter()
        del key_cache_layer
        del attention
        total_time += (end_time - start_time) * 1000
    return total_time


# In[10]:


@njit
def rmsnorm_part1_nb(input, weight):
    ss = 0
    for i in range(len(input)):
        ss += input[i] * input[i]
    return ss


def rmsnorm_part1_runner(weights, inputs, f=None):
    total_time = 0
    for i in range(len(inputs)):
        inp = inputs[i].flatten()
        w = weights[i].flatten()

        rmsnorm_part1_nb(inp, w)
        start_time = time.perf_counter()
        rmsnorm_part1_nb(inp, w)
        end_time = time.perf_counter()
        del w
        del inp
        total_time += (end_time - start_time) * 1000
    return total_time


# In[11]:


@njit
def rmsnorm_part2_nb(input, weight, ss):
    output = []
    size = len(input)
    inv_ss = 1 / math.sqrt(ss / size + 1)
    for i in range(size):
        output.append(inv_ss * input[i] * weight[i])
    return output


def rmsnorm_part2_runner(weights, inputs, f=None):
    total_time = 0
    for i in range(len(inputs)):
        inp = inputs[i].flatten()
        w = weights[i].flatten()
        ss = np.sum(inp * inp)

        rmsnorm_part2_nb(inp, w, ss)
        start_time = time.perf_counter()
        rmsnorm_part2_nb(inp, w, ss)
        end_time = time.perf_counter()
        del w
        del inp
        total_time += (end_time - start_time) * 1000
    return total_time


# In[12]:


@njit
def silu_nb(input, hidden_dim):
    output = []
    for i in range(hidden_dim):
        curr = 1 / (1 + math.exp(-input[i])) * input[i]
        output.append(curr)
    return output


def silu_runner(inputs, _, f=None):
    total_time = 0
    for i in range(len(inputs)):
        inp = inputs[i].flatten()
        hidden_dim = len(inp)

        silu_nb(inp, hidden_dim)
        start_time = time.perf_counter()
        silu_nb(inp, hidden_dim)
        end_time = time.perf_counter()
        del inp
        total_time += (end_time - start_time) * 1000
    return total_time


# In[13]:


@njit
def softmax_part1_nb(input, max_pos):
    max_val = input[0]
    for i in range(1, max_pos):
        if input[i] > max_val:
            max_val = input[i]
    return max_val


def softmax_part1_runner(inputs, _, f=None):
    total_time = 0
    for i in range(len(inputs)):
        inp = inputs[i].flatten()
        max_pos = len(inp)

        softmax_part1_nb(inp, max_pos)
        start_time = time.perf_counter()
        softmax_part1_nb(inp, max_pos)
        end_time = time.perf_counter()
        del inp
        total_time += (end_time - start_time) * 1000
    return total_time


# In[14]:


@njit
def softmax_part2_nb(input, max_pos, max_val):
    output = []
    for i in range(max_pos):
        cur = math.exp(input[i] - max_val)
        output.append(cur)
    return output


def softmax_part2_runner(inputs, _, f=None):
    total_time = 0
    for i in range(len(inputs)):
        inp = inputs[i].flatten()
        max_pos = len(inp)

        max_val = np.max(inp[:max_pos])

        softmax_part2_nb(inp, max_pos, max_val)
        start_time = time.perf_counter()
        softmax_part2_nb(inp, max_pos, max_val)
        end_time = time.perf_counter()
        del inp
        total_time += (end_time - start_time) * 1000
    return total_time


# In[15]:


@njit
def softmax_part3_nb(output, max_pos):
    sum = 0
    for i in range(max_pos):
        sum += output[i]
    return sum


def softmax_part3_runner(inputs, _, f=None):
    total_time = 0
    for i in range(len(inputs)):
        inp = inputs[i].flatten()
        max_pos = len(inp)
        outp = np.exp(inp[:max_pos] - np.max(inp[:max_pos]))

        softmax_part3_nb(outp, max_pos)
        start_time = time.perf_counter()
        softmax_part3_nb(outp, max_pos)
        end_time = time.perf_counter()
        del outp
        total_time += (end_time - start_time) * 1000
    return total_time


# In[16]:


@njit
def softmax_part4_nb(unnormalized_output, max_pos, sum):
    output = []
    for i in range(max_pos):
        output.append(unnormalized_output[i] / sum)
    return output


def softmax_part4_runner(inputs, _, f=None):
    total_time = 0
    for i in range(len(inputs)):
        inp = inputs[i].flatten()
        max_pos = len(inp)
        outp = np.exp(inp[:max_pos] - np.max(inp[:max_pos]))
        sum = np.sum(outp[:max_pos])

        softmax_part4_nb(outp, max_pos, sum)
        start_time = time.perf_counter()
        softmax_part4_nb(outp, max_pos, sum)
        end_time = time.perf_counter()
        del outp
        total_time += (end_time - start_time) * 1000
    return total_time


# # In[17]:


# timer(weights, w_input, None, elewise_mul_runner)


# # In[ ]:


# timer(attn_weights, aw_input, None, matmul_runner)


# # In[ ]:


# timer(k_weights, q_weights, None, multiquery_attention_part1_runner)


# In[ ]:


timer(k_weights, q_weights, None, multiquery_attention_part2_runner)


# In[ ]:


timer(weights, w_input, None, rmsnorm_part1_runner)


# In[ ]:


timer(weights, w_input, None, rmsnorm_part2_runner)


# In[ ]:


timer(weights, None, None, silu_runner)


# In[ ]:


timer(attn_weights, None, None, softmax_part1_runner)


# In[ ]:


timer(attn_weights, None, None, softmax_part2_runner)


# In[ ]:


timer(attn_weights, None, None, softmax_part3_runner)


# In[ ]:


timer(attn_weights, None, None, softmax_part4_runner)
