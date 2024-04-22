####### import statements ########
import numpy as np


def transformer_part4_np(input1, input2, hidden_dim):
    return (input1[:hidden_dim]) * (input2[:hidden_dim])


def transformer_part4_np_glued(input1, input2, hidden_dim):
    input1 = np.array(input1).astype(np.float32)
    input2 = np.array(input2).astype(np.float32)
    return transformer_part4_np(input1, input2, hidden_dim)
