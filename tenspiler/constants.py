from tenspiler_common import (
    firsts_fn_decl,
    integer_exp_fn_decl,
    integer_sqrt_fn_decl,
    integer_sqrt_helper_fn_decl,
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
        ]
    )
)
TENSPILER_FNS = sorted(_UNSORTED_TENSPILER_FNS, key=lambda x: x.name())
