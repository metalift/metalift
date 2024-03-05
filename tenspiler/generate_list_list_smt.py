from tenspiler_common import (
    firsts_fn_decl,
    list_list_col_slice_fn_decl,
    list_list_col_slice_with_length_fn_decl,
    list_list_slice_fn_decl,
    list_list_slice_with_length_fn_decl,
    list_slice_fn_decl,
    list_slice_with_length_fn_decl,
    matrix_transpose_fn_decl,
    rests_fn_decl,
)

from metalift.ir import fn_decl

fn_decls = [
    list_slice_fn_decl,
    list_slice_with_length_fn_decl,
    list_list_slice_fn_decl,
    list_list_slice_with_length_fn_decl,
    list_list_col_slice_fn_decl,
    list_list_col_slice_with_length_fn_decl,
    firsts_fn_decl,
    rests_fn_decl,
    matrix_transpose_fn_decl,
]
with open("list_listi.smt", "w") as f:
    for fn_decl in fn_decls:
        f.write(fn_decl.toSMT())
        f.write("\n\n")
