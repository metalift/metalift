#!/usr/bin/env python
# coding: utf-8

# In[1]:


import os
import time

import cv2
import numpy as np
from numba import njit

# In[2]:


rng = np.random.default_rng(1)

# In[3]:


folder = "./data/"

img_files = [
    os.path.join(folder, f)
    for f in os.listdir(folder)
    if os.path.isfile(os.path.join(folder, f))
]

bases = []
actives = []

for _file in img_files:
    img = cv2.imread(_file, cv2.IMREAD_GRAYSCALE).astype(np.uint8)
    rnd = (rng.random(img.shape, dtype=np.float32) * 255).astype(np.uint8)
    bases.append(img)
    actives.append(rnd)

# In[4]:


def mat_runner(bases, actives, f):
    total_time = 0
    for i in range(len(bases)):
        b = bases[i]
        a = actives[i]
        start_time = time.perf_counter()
        f(b, a)
        end_time = time.perf_counter()
        del a
        del b
        total_time += (end_time - start_time) * 1000
    return total_time


def vec_runner_int(bases, actives, f):
    total_time = 0
    for i in range(len(bases)):
        b = bases[i].flatten()
        a = actives[i].flatten()
        opacity = rng.random(1, dtype=np.float32).astype(np.uint8)
        start_time = time.perf_counter()
        f(b, a, opacity)
        end_time = time.perf_counter()
        del a
        del b
        total_time += (end_time - start_time) * 1000
    return total_time


def vec_runner_float(bases, actives, f):
    total_time = 0
    for i in range(len(bases)):
        b = bases[i].flatten()
        a = actives[i].flatten()
        opacity = rng.random(1, dtype=np.float32)
        start_time = time.perf_counter()
        f(b, a, opacity)
        end_time = time.perf_counter()
        del a
        del b
        total_time += (end_time - start_time) * 1000
    return total_time


def timer(input1, input2, f, runner):
    runs = 10
    times = []
    for i in range(runs):
        if i == 0:
            print("first run, skipping")
            continue
        print(f"{i}th run ------")
        times.append(runner(input1, input2, f))
        times_seen_so_far = np.array(times)
        print(f"{f.__name__}")
        print(f"{np.average(times_seen_so_far)}ms +/- {np.std(times_seen_so_far)}ms")


# In[5]:


### Nested

# In[6]:


@njit
def darken_blend_8_np(base, active):
    return np.where(np.greater(base, active), active, base)


# In[7]:


@njit
def color_burn_8_np(base, active):
    return np.where(np.equal(active, 0), 255, 255 - (255 - base) // active)


# In[8]:


@njit
def lighten_blend_8_np(base, active):
    return np.where(np.less(base, active), active, base)


# In[9]:


@njit
def color_dodge_8_np(base, active):
    return np.where(np.equal(active, 255), 255, base // (255 - active))


# In[10]:


@njit
def overlay_blend_8_np(base, active):
    return np.where(
        np.greater_equal(base, 128),
        2 * base + base - 2 * base * base // 255 - 128,
        2 * base * base // 128,
    )


# In[11]:


@njit
def multiply_blend_8_np(base, active):
    return base * active // 255


# In[12]:


@njit
def linear_burn_8_np(base, active):
    return base + active - 255


# In[13]:


@njit
def screen_blend_8_np(base, active):
    return base + active - base * active // 255


# In[14]:


@njit
def linear_dodge_8_np(base, active):
    return base + active


# In[15]:


### Single

# In[16]:


@njit
def normal_blend_f_np(base, active, opacity):
    return opacity * active + (1 - opacity) * base


# In[17]:


@njit
def normal_blend_8_np(base, active, opacity):
    return opacity * active + (255 - opacity) * base


# In[18]:


timer(bases, actives, darken_blend_8_np, mat_runner)

# In[19]:


timer(bases, actives, color_burn_8_np, mat_runner)

# In[20]:


timer(bases, actives, lighten_blend_8_np, mat_runner)

# In[21]:


timer(bases, actives, color_dodge_8_np, mat_runner)

# In[22]:


timer(bases, actives, overlay_blend_8_np, mat_runner)

# In[23]:


timer(bases, actives, multiply_blend_8_np, mat_runner)

# In[24]:


timer(bases, actives, linear_burn_8_np, mat_runner)

# In[25]:


timer(bases, actives, screen_blend_8_np, mat_runner)

# In[26]:


timer(bases, actives, linear_dodge_8_np, mat_runner)

# In[27]:


timer(bases, actives, normal_blend_f_np, vec_runner_float)

# In[28]:


timer(bases, actives, normal_blend_8_np, vec_runner_int)
