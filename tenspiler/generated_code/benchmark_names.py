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
    # "matmul",
    # "rmsnorm_part1",
    # "rmsnorm_part2",
    "softmax_part1",
    "softmax_part2",
    "softmax_part3",
    "softmax_part4",
    "transformer_part1",
    "transformer_part2",
    "transformer_part3",
    "transformer_part4",
]
blas_test_name = ["dot", "gemv"]
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
dsp_test_name = [
    "matadd",
    "matscal",
    "matsub",
    "vadd",
    "vcopy",
    "vmul",
    "vneg",
    "voffset",
    "vrecip",
    "vscal",
    "vsub",
    "wvec",
]
dspstone_test_name = ["mat1x3", "n_real_updates"]
makespeare_test_name = ["sum_of_squares"]
mathfu_test_name = [
    "diveq",
    "diveq_sca",
    "len",
    "len_sq",
    "matmul_sca",
    "muleq",
    "muleq_sca",
    "negate",
    "pluseq",
    "subeq",
    "subeq_sca",
]
simpl_array_test_name = [
    "array_inc",
    "array_sum",
    "cube_in_place",
    "fourth_in_place",
    "sum_elts",
]
utdsp_test_name = ["fir_small", "lmsfir1", "lmsfir2"]
all_test = (
    llama_test_name
    + blas_test_name
    + darknet_test_name
    + dsp_test_name
    + dspstone_test_name
    + makespeare_test_name
    + mathfu_test_name
    + simpl_array_test_name
    + utdsp_test_name
)
gemmini_not_comp = [
    "translate_array",
    "vcopy",
    "vmul",
    "vneg",
    "voffset",
    "vrecip",
    "diveq",
    "muleq",
    "negate",
    "subeq_sca",
    "array_inc",
    "cube_in_place",
    "fourth_in_place",
]
gemmini_blend_func_names = [
    'normal_blend_8',
    'normal_blend_f',
    'linear_burn_8',
    'linear_dodge_8',
    'screen_blend_8',
]
gemmini_llama_func_names = ['softmax_part3', 'rmsnorm_part1', 'matmul']