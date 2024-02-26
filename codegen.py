# vec_elemwise_mul(arg1, arg2) => torch.multiply(arg1, arg2),
# mx.multiply
# tf.multiply
# np.multiply

# matrix_vec_mul(mat, vec)-> torch.matmul(mat, vec)
# mx.matmul
# tf.linalg.matvec
# np.matmul

# matrix_transpose(mat)->torch.transpose(mat, 0, 1)
# mx.transpose()
# tf.transpose()
# np.transpose()

# reduce_sum=>torch.sum
# mx.sum
# tf.reduce_sum
# np.sum

# vec_scalar_mul(a, b)=>torch.multiply(a, b)
# mx.multiply
# tf.multiply
# np.multiply

# test_sqrt=>torch.sqrt(torch.as_tensor())
# mx.sqrt
# tf.sqrt
# np.sqrt

# list_length(inp)=> inp.size(dim=0) pytorch
# inp.size mlx
# tf.size(input, tf.float32) tensorflow
# inp.size numpy

# scalar_vec_div => torch.divide
# mx.divide
# tf.divide
# np.divide

# vec_map(list, map_int_to_int)
# map_int_to_int is defined separatly, torch.sqrt(torch.as_tensor()) or torch.exp()
# mx.sqrt(mx.array([])) or mx.exp
# tf.sqrt(tf.cast(, tf.float32)) or tf.exp()
# np.sqrt or np.exp

# reduce_max => torch.max
# mx.max
# tf.reduce_max
# np.max

# rand() special constant =>  torch.randint(1, 2147483647, base.shape, dtype=torch.int32,device='cuda')
# mx.random.randint(1, 2147483647, base.shape, mx.int32)
# tf.random.uniform(tf.shape(base), 1, 2147483647)
# np.random.randint(1, 2147483647, base.shape)


# vec_scalar_sub => inp1 - scal
# vec_scalar_div(vec, scalar) => vec/scalar
# vec_scalar_add => a + b
# list_col_slice_with_length(mat, start, length)=>mat[:, start:start + length]
# list_slice_with_length(vec, start, length) => vec[start: start + length]
# list_take => arg1[:arg2]
