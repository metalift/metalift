# NKI_EXAMPLE_42_BEGIN

import neuronxcc.nki as nki
import neuronxcc.nki.isa as nisa
import neuronxcc.nki.language as nl
import numpy as np


def row_indices_ref(width):
    ip = nl.arange(1)[:, None]
    iy = nl.arange(width)[None, :]
    return ip, iy


def row_dst_ref(out_tensor, row_idx):
    ip, iy = row_indices_ref(out_tensor.shape[1])
    return out_tensor[row_idx + ip, iy]


def square_ref(a_tensor, out_tensor):
    assert a_tensor.shape[0] == 1
    ip, iy = row_indices_ref(a_tensor.shape[1])
    a_tile = nl.load(a_tensor[ip, iy])
    result = nisa.tensor_tensor(a_tile, a_tile, op=np.multiply)
    nl.store(out_tensor[ip, iy], value=result)


def mean_ref(a_tensor, out_tensor):
    assert a_tensor.shape[0] == 1
    ip, iy = row_indices_ref(a_tensor.shape[1])
    iw = nl.arange(1)[None, :]
    a_tile = nl.load(a_tensor[ip, iy])
    result = (
        nisa.tensor_reduce(op=np.add, data=a_tile, axis=1, keepdims=True)
        / a_tensor.shape[1]
    )
    nl.store(out_tensor[ip, iw], value=result)


def rsqrt_ref(a_tensor, out_tensor):
    assert a_tensor.shape == (1, 1)
    ip, _ = row_indices_ref(1)
    iw = nl.arange(1)[None, :]
    a_tile = nl.load(a_tensor[ip, iw])
    result = nisa.activation(op=nl.rsqrt, data=a_tile)
    nl.store(out_tensor[ip, iw], value=result)


def col_multiply_ref(a_tensor, b_tensor, out_tensor):
    assert a_tensor.shape[0] == 1
    assert b_tensor.shape == (1, 1)
    ip, iy = row_indices_ref(a_tensor.shape[1])
    iw = nl.arange(1)[None, :]
    a_tile = nl.load(a_tensor[ip, iy])
    b_tile = nl.load(b_tensor[ip, iw])
    b_bcast = b_tile.broadcast_to(a_tensor.shape)
    result = nisa.tensor_tensor(a_tile, b_bcast, op=np.multiply)
    nl.store(out_tensor[ip, iy], value=result)


def row_multiply_ref(a_tensor, g_tensor, out_tensor):
    assert a_tensor.shape[0] == 1
    ip, iy = row_indices_ref(a_tensor.shape[1])
    a_tile = nl.load(a_tensor[ip, iy])
    g_tile = nl.load(g_tensor.reshape((1, g_tensor.shape[0]))[ip, iy])
    result = nisa.tensor_tensor(a_tile, g_tile, op=np.multiply)
    nl.store(out_tensor[ip, iy], value=result)


def write_row_ref(out_tensor, row_idx, row_tensor):
    ip, iy = row_indices_ref(row_tensor.shape[1])
    nl.store(row_dst_ref(out_tensor, row_idx), value=nl.load(row_tensor[ip, iy]))


@nki.jit
def ref(a_tensor, weight):
    # RMSNorm with per-row 1D helper functions, shared_hbm pre-allocated.
    N = a_tensor.shape[1]

    out_tensor = nl.ndarray(a_tensor.shape, dtype=a_tensor.dtype, buffer=nl.shared_hbm)
    input = nl.ndarray((1, N), dtype=a_tensor.dtype, buffer=nl.shared_hbm)
    input_squared_buf = nl.ndarray((1, N), dtype=a_tensor.dtype, buffer=nl.shared_hbm)
    input_squared_buf_mean_buf = nl.ndarray(
        (1, 1), dtype=a_tensor.dtype, buffer=nl.shared_hbm
    )
    input_squared_buf_mean_buf_rsqrt_buf = nl.ndarray(
        (1, 1), dtype=a_tensor.dtype, buffer=nl.shared_hbm
    )
    input_weight_elemwise_mul_buf = nl.ndarray(
        (1, N), dtype=a_tensor.dtype, buffer=nl.shared_hbm
    )
    input_weight_elemwise_mul_buf_input_squared_buf_mean_buf_rsqrt_buf_scaled_buf = (
        nl.ndarray((1, N), dtype=a_tensor.dtype, buffer=nl.shared_hbm)
    )

    for i in nl.sequential_range(a_tensor.shape[0]):
        input = a_tensor[i : i + 1, :]
        square_ref(input, input_squared_buf)
        mean_ref(input_squared_buf, input_squared_buf_mean_buf)
        rsqrt_ref(input_squared_buf_mean_buf, input_squared_buf_mean_buf_rsqrt_buf)
        row_multiply_ref(input, weight, input_weight_elemwise_mul_buf)
        col_multiply_ref(
            input_weight_elemwise_mul_buf,
            input_squared_buf_mean_buf_rsqrt_buf,
            input_weight_elemwise_mul_buf_input_squared_buf_mean_buf_rsqrt_buf_scaled_buf,
        )
        write_row_ref(
            out_tensor,
            i,
            input_weight_elemwise_mul_buf_input_squared_buf_mean_buf_rsqrt_buf_scaled_buf,
        )

    return out_tensor
