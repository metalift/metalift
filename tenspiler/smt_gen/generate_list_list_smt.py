from metalift.ir import fn_decl
from tenspiler.tenspiler_common import (
    firsts_fn_decl,
    matrix_col_slice_fn_decl,
    matrix_col_slice_with_length_fn_decl,
    matrix_row_slice_fn_decl,
    matrix_row_slice_with_length_fn_decl,
    matrix_transpose_fn_decl,
    rests_fn_decl,
    vec_slice_fn_decl,
    vec_slice_with_length_fn_decl,
)

fn_decls = [
    vec_slice_fn_decl,
    vec_slice_with_length_fn_decl,
    matrix_row_slice_fn_decl,
    matrix_row_slice_with_length_fn_decl,
    matrix_col_slice_fn_decl,
    matrix_col_slice_with_length_fn_decl,
    firsts_fn_decl,
    rests_fn_decl,
    matrix_transpose_fn_decl,
]
with open("matrixi.smt", "w") as f:
    for fn_decl in fn_decls:
        f.write(fn_decl.toSMT())
        f.write("\n\n")
