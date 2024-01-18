#!/usr/bin/env python
# coding: utf-8

# In[1]:


import time

import h5py
import numpy as np

# In[2]:


rng = np.random.default_rng(1)


# In[3]:


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


# In[4]:


def timer(input1, input2, f, runner):
    runs = 10
    times = []
    for _ in range(runs):
        times.append(runner(input1, input2, f))
    times = np.array(times)
    print(f"{runner.__name__[:-6]}np")
    print(f"{np.average(times)}ms +/- {np.std(times)}ms")


# In[5]:


def elewise_mul_np(input1, input2, hidden_dim):
    return np.multiply(input1[:hidden_dim], input2[:hidden_dim])


def elewise_mul_runner(inputs1, inputs2, f=None):
    total_time = 0
    for i in range(len(inputs1)):
        inp1 = inputs1[i].flatten()
        inp2 = inputs2[i].flatten()
        hidden_dim = len(inp1)

        start_time = time.perf_counter()
        elewise_mul_np(inp1, inp2, hidden_dim)
        end_time = time.perf_counter()
        del inp2
        del inp1
        total_time += (end_time - start_time) * 1000
    return total_time


# In[6]:


def matmul_np(weight, input):
    return np.matmul(weight, input)


def matmul_runner(weights, inputs, f=None):
    total_time = 0
    for i in range(len(inputs)):
        w = weights[i]
        inp = inputs[i]

        start_time = time.perf_counter()
        matmul_np(w, inp)
        end_time = time.perf_counter()
        del inp
        del w
        total_time += (end_time - start_time) * 1000
    return total_time


# In[7]:


def multiquery_attention_part1_np(token_position, head, head_size, key_cache_layer, q):
    return np.matmul(
        key_cache_layer[:token_position][
            :, (head * head_size) : (head * head_size) + head_size
        ],
        q[(head * head_size) : (head * head_size) + head_size],
    ) / np.sqrt(head_size * 1)


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

        start_time = time.perf_counter()
        multiquery_attention_part1_np(
            token_position, head, head_size, key_cache_layer, q
        )
        end_time = time.perf_counter()
        del key_cache_layer
        del q
        total_time += (end_time - start_time) * 1000
    return total_time


# In[22]:


def multiquery_attention_part2_np(
    token_position, head, head_size, key_cache_layer, attention
):
    return np.matmul(
        np.transpose(
            key_cache_layer[: token_position + 1][
                :, (head * head_size) : (head * head_size) + head_size
            ]
        ),
        attention[: token_position + 1],
    )


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

        attention = multiquery_attention_part1_np(
            token_position, head, head_size, key_cache_layer, q
        )
        attention = np.append(attention, np.array([0]))

        start_time = time.perf_counter()
        multiquery_attention_part2_np(
            token_position, head, head_size, key_cache_layer, attention
        )
        end_time = time.perf_counter()
        del key_cache_layer
        del attention
        total_time += (end_time - start_time) * 1000
    return total_time


# In[9]:


def rmsnorm_part1_np(input, weight):
    return np.sum(np.multiply(input, input))


def rmsnorm_part1_runner(weights, inputs, f=None):
    total_time = 0
    for i in range(len(inputs)):
        inp = inputs[i].flatten()
        w = weights[i].flatten()

        start_time = time.perf_counter()
        rmsnorm_part1_np(inp, w)
        end_time = time.perf_counter()
        del w
        del inp
        total_time += (end_time - start_time) * 1000
    return total_time


# In[10]:


def rmsnorm_part2_np(input, weight, ss):
    return np.multiply((1 / np.sqrt((ss / input.size) + 1)), np.multiply(input, weight))


def rmsnorm_part2_runner(weights, inputs, f=None):
    total_time = 0
    for i in range(len(inputs)):
        inp = inputs[i].flatten()
        w = weights[i].flatten()
        ss = np.sum(inp * inp)

        start_time = time.perf_counter()
        rmsnorm_part2_np(inp, w, ss)
        end_time = time.perf_counter()
        del w
        del inp
        total_time += (end_time - start_time) * 1000
    return total_time


# In[11]:


def silu_np(input, hidden_dim):
    return np.multiply(
        np.divide(1, (np.exp(-1 * input[:hidden_dim]) + 1)), input[:hidden_dim]
    )


def silu_runner(inputs, _, f=None):
    total_time = 0
    for i in range(len(inputs)):
        inp = inputs[i].flatten()
        hidden_dim = len(inp)

        start_time = time.perf_counter()
        silu_np(inp, hidden_dim)
        end_time = time.perf_counter()
        del inp
        total_time += (end_time - start_time) * 1000
    return total_time


# In[12]:


def softmax_part1_np(input, max_pos):
    return np.max(input[:max_pos])


def softmax_part1_runner(inputs, _, f=None):
    total_time = 0
    for i in range(len(inputs)):
        inp = inputs[i].flatten()
        max_pos = len(inp)

        start_time = time.perf_counter()
        softmax_part1_np(inp, max_pos)
        end_time = time.perf_counter()
        del inp
        total_time += (end_time - start_time) * 1000
    return total_time


# In[13]:


def softmax_part2_np(input, max_pos, max_val):
    return np.exp(input[:max_pos] - max_val)


def softmax_part2_runner(inputs, _, f=None):
    total_time = 0
    for i in range(len(inputs)):
        inp = inputs[i].flatten()
        max_pos = len(inp)

        max_val = np.max(inp[:max_pos])

        start_time = time.perf_counter()
        softmax_part2_np(inp, max_pos, max_val)
        end_time = time.perf_counter()
        del inp
        total_time += (end_time - start_time) * 1000
    return total_time


# In[14]:


def softmax_part3_np(output, max_pos):
    return np.sum(output[:max_pos])


def softmax_part3_runner(inputs, _, f=None):
    total_time = 0
    for i in range(len(inputs)):
        inp = inputs[i].flatten()
        max_pos = len(inp)
        outp = np.exp(inp[:max_pos] - np.max(inp[:max_pos]))

        start_time = time.perf_counter()
        softmax_part3_np(outp, max_pos)
        end_time = time.perf_counter()
        del outp
        total_time += (end_time - start_time) * 1000
    return total_time


# In[15]:


def softmax_part4_np(unnormalized_output, max_pos, sum):
    return unnormalized_output[:max_pos] / sum


def softmax_part4_runner(inputs, _, f=None):
    total_time = 0
    for i in range(len(inputs)):
        inp = inputs[i].flatten()
        max_pos = len(inp)
        outp = np.exp(inp[:max_pos] - np.max(inp[:max_pos]))
        sum = np.sum(outp[:max_pos])

        start_time = time.perf_counter()
        softmax_part4_np(outp, max_pos, sum)
        end_time = time.perf_counter()
        del outp
        total_time += (end_time - start_time) * 1000
    return total_time


timer(attn_weights, None, None, softmax_part4_runner)
exit(0)

# In[16]:


timer(weights, w_input, None, elewise_mul_runner)


# In[17]:


timer(attn_weights, aw_input, None, matmul_runner)


# In[18]:


timer(k_weights, q_weights, None, multiquery_attention_part1_runner)


# In[23]:


timer(k_weights, q_weights, None, multiquery_attention_part2_runner)


# In[24]:


timer(weights, w_input, None, rmsnorm_part1_runner)


# In[25]:


timer(weights, w_input, None, rmsnorm_part2_runner)


# In[26]:


timer(weights, None, None, silu_runner)


# In[27]:


timer(attn_weights, None, None, softmax_part1_runner)


# In[28]:


timer(attn_weights, None, None, softmax_part2_runner)


# In[29]:


timer(attn_weights, None, None, softmax_part3_runner)


# In[30]:


timer(attn_weights, None, None, softmax_part4_runner)
