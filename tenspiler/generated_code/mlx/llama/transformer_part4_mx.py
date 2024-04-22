
####### import statements ########
import mlx.core as mx

def transformer_part4_mx (input1, input2, hidden_dim):
    return (input1[:hidden_dim]) * (input2[:hidden_dim])

def transformer_part4_mx_glued (input1, input2, hidden_dim):
    input1 = mx.array(input1, mx.float32)
    input2 = mx.array(input2, mx.float32)
    return transformer_part4_mx(input1, input2, hidden_dim)
