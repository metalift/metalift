blend_test_name = [
    "color_burn_8",
    "color_dodge_8",
    "darken_blend_8",
    "dissolve_blend_8",
    "lighten_blend_8",
    "linear_burn_8",
    "linear_dodge_8",
    "multiply_blend_8",
    "normal_blend_8",
    "normal_blend_f",
    "overlay_blend_8",
    "screen_blend_8",
]

llama_test_name = [
    "matmul",
    "rmsnorm_part1",
    "rmsnorm_part2",
    "softmax_part1",
    "softmax_part2",
    "softmax_part3",
    "softmax_part4",
    "transformer_part1",
    "transformer_part2",
    "transformer_part3",
    "transformer_part4",
]

darknet_test_name = [
    "mag_array",
    "matrix_add_matrix",
    "mse_array",
    "mult_add_into_cpu",
    "ol_l2_cpu1",
    "ol_l2_cpu2",
    "scale_array",
    "scale_matrix",
    "sum_array",
    "translate_array",
]

utdsp_test_name = ["fir_small", "lmsfir1", "lmsfir2"]
all_test = blend_test_name + llama_test_name + darknet_test_name + utdsp_test_name
gemmini_not_comp = [
    "translate_array",
]
gemmini_blend_func_names = [
    "normal_blend_8",
    "normal_blend_f",
    "linear_burn_8",
    "linear_dodge_8",
    "screen_blend_8",
]
gemmini_llama_func_names = ["softmax_part3", "rmsnorm_part1", "matmul"]
