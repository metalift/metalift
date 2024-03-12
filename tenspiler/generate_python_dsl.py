from tenspiler_common import (
    MAP_INT_TO_INT,
    firsts_fn_decl,
    list_list_col_slice_fn_decl,
    list_list_col_slice_with_length_fn_decl,
    list_list_slice_fn_decl,
    list_list_slice_with_length_fn_decl,
    list_slice_fn_decl,
    list_slice_with_length_fn_decl,
    matrix_matrix_to_matrix_target_lang,
    matrix_selection_two_args_fn_decl,
    matrix_transpose_fn_decl,
    matrix_vec_to_vec_target_lang,
    rests_fn_decl,
    scalar_matrix_to_matrix_target_lang,
    scalar_vec_to_vec_target_lang,
    selection_two_args_fn_decl,
    vec_to_int_target_lang,
    vec_to_vec_target_lang,
    vec_vec_to_vec_target_lang,
)

for fn in [
    *vec_to_int_target_lang,
    *matrix_vec_to_vec_target_lang,
    *vec_vec_to_vec_target_lang,
    *matrix_matrix_to_matrix_target_lang,
    *scalar_vec_to_vec_target_lang,
    *scalar_matrix_to_matrix_target_lang,
    *vec_to_vec_target_lang,
    matrix_selection_two_args_fn_decl,
    selection_two_args_fn_decl,
    list_slice_fn_decl,
    list_slice_with_length_fn_decl,
    list_list_slice_fn_decl,
    list_list_slice_with_length_fn_decl,
    list_list_col_slice_fn_decl,
    list_list_col_slice_with_length_fn_decl,
    firsts_fn_decl,
    rests_fn_decl,
    matrix_transpose_fn_decl,
]:
    if fn.name() == MAP_INT_TO_INT:
        continue
    python_fn = fn.to_python()
    print(python_fn)
    print()
