
####### import statements ########
import mlx.core as mx

def transformer_part3_mx (input, hidden_dim):
    return (input[:hidden_dim]) * ((1) / ((1) + (mx.exp((0) - (input[:hidden_dim])))))

def transformer_part3_mx_glued (input, hidden_dim):
    input = mx.array(input, mx.float32)
    return transformer_part3_mx(input, hidden_dim)
