from metalift.utils.tenspiler.axioms import (
    dissolve_matrix_selection_two_args_axiom,
    matrix_elemwise_add_axiom,
    matrix_elemwise_mul_axiom,
    matrix_elemwise_sub_axiom,
    matrix_scalar_div_axiom,
    matrix_scalar_mul_axiom,
    matrix_scalar_sub_axiom,
    matrix_selection_two_args_axiom,
    matrix_vec_mul_axiom,
    reduce_max_axiom,
    reduce_sum_axiom,
    scalar_vec_div_axiom,
    scalar_vec_sub_axiom,
    vec_elemwise_add_axiom,
    vec_elemwise_div_axiom,
    vec_elemwise_mul_axiom,
    vec_elemwise_sub_axiom,
    vec_scalar_add_axiom,
    vec_scalar_div_axiom,
    vec_scalar_mul_axiom,
    vec_scalar_sub_axiom,
)
from metalift.utils.tenspiler.tenspiler_common import (
    firsts_fn_decl,
    integer_exp_fn_decl,
    integer_sqrt_fn_decl,
    integer_sqrt_helper_fn_decl,
    ite_int,
    matrix_col_slice_fn_decl,
    matrix_matrix_to_matrix_target_lang,
    matrix_row_slice_fn_decl,
    matrix_selection_two_args_fn_decl,
    matrix_transpose_fn_decl,
    matrix_vec_to_vec_target_lang,
    rests_fn_decl,
    scalar_matrix_to_matrix_target_lang,
    scalar_vec_to_vec_target_lang,
    selection_two_args_fn_decl,
    vec_slice_fn_decl,
    vec_to_int_target_lang,
    vec_to_vec_target_lang,
    vec_vec_to_vec_target_lang,
)

_UNSORTED_TENSPILER_FNS = list(
    set(
        [
            *vec_to_int_target_lang,
            *matrix_vec_to_vec_target_lang,
            *vec_vec_to_vec_target_lang,
            *matrix_matrix_to_matrix_target_lang,
            *scalar_vec_to_vec_target_lang,
            *scalar_matrix_to_matrix_target_lang,
            *vec_to_vec_target_lang,
            matrix_selection_two_args_fn_decl,
            selection_two_args_fn_decl,
            vec_slice_fn_decl,
            matrix_row_slice_fn_decl,
            matrix_col_slice_fn_decl,
            firsts_fn_decl,
            rests_fn_decl,
            matrix_transpose_fn_decl,
            integer_exp_fn_decl,
            integer_sqrt_helper_fn_decl,
            integer_sqrt_fn_decl,
            ite_int,
        ]
    )
)
_NOT_NONE_UNSORTED_TENSPILER_FNS = [
    fn for fn in _UNSORTED_TENSPILER_FNS if fn.body() is not None
]
TENSPILER_FNS = sorted(_NOT_NONE_UNSORTED_TENSPILER_FNS, key=lambda x: x.name())
TENSPILER_FN_NAME_TO_AXIOMS = {
    "matrix_elemwise_add": [matrix_elemwise_add_axiom],
    "vec_elemwise_add": [vec_elemwise_add_axiom],
    "vec_elemwise_mul": [vec_elemwise_mul_axiom],
    "scalar_vec_sub": [scalar_vec_sub_axiom],
    "vec_scalar_sub": [vec_scalar_sub_axiom],
    "vec_scalar_add": [vec_scalar_add_axiom],
    "scalar_vec_div": [scalar_vec_div_axiom],
    "vec_scalar_mul": [vec_scalar_mul_axiom],
    "vec_elemwise_sub": [vec_elemwise_sub_axiom],
    "reduce_sum": [reduce_sum_axiom],
    "reduce_max": [reduce_max_axiom],
    "vec_scalar_div": [vec_scalar_div_axiom],
    "vec_elemwise_div": [vec_elemwise_div_axiom],
    "matrix_elemwise_add": [matrix_elemwise_add_axiom],
    "matrix_elemwise_sub": [matrix_elemwise_sub_axiom],
    "matrix_scalar_mul": [matrix_scalar_mul_axiom],
    "matrix_vec_mul": [matrix_vec_mul_axiom],
    "matrix_elemwise_mul": [matrix_elemwise_mul_axiom],
    "matrix_scalar_div": [matrix_scalar_div_axiom],
    "matrix_scalar_sub": [matrix_scalar_sub_axiom],
    "matrix_selection_two_args": [matrix_selection_two_args_axiom],
    "dissolve_matrix_selection_two_args": [dissolve_matrix_selection_two_args_axiom],
}
