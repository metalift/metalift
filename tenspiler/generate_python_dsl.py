from tenspiler.tenspiler_common import (
    MAP_INT_TO_INT,
    matrix_selection_two_args_fn_decl,
    selection_two_args_fn_decl,
)

for fn in [
    # *vec_to_int_target_lang,
    # *matrix_vec_to_vec_target_lang,
    # *vec_vec_to_vec_target_lang,
    # *matrix_matrix_to_matrix_target_lang,
    # *scalar_vec_to_vec_target_lang,
    # *scalar_matrix_to_matrix_target_lang,
    # *vec_to_vec_target_lang,
    matrix_selection_two_args_fn_decl,
    selection_two_args_fn_decl,
]:
    if fn.name() == MAP_INT_TO_INT:
        continue
    python_fn = fn.to_python()
    print(python_fn)
    print()
