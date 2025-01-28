from metalift.ir import Int
from metalift.ir import List as mlList
from metalift.ir import Matrix, call, fn_decl, fn_decl_recursive, ite

# Define some arguments to be used
lst = mlList(Int, "lst")
matrix = Matrix(Int, "matrix")
start = Int("start")
end = Int("end")
lst_length = Int("lst_length")

# list_slice
list_slice_fn_decl = fn_decl(
    "list_slice", mlList[Int], lst[:end][:start:], lst, start, end
)

# list_slice_with_length
list_slice_with_length_fn_decl = fn_decl(
    "list_slice_with_length",
    mlList[Int],
    lst[start : start + lst_length],
    lst,
    start,
    lst_length,
)

# list_list_slice
list_list_slice_fn_decl = fn_decl(
    "list_list_slice", Matrix[Int], matrix[:end][:start:], matrix, start, end
)

# list_slice_with_length
list_list_slice_with_length_fn_decl = fn_decl(
    "list_list_slice_with_length",
    Matrix[Int],
    matrix[start : start + lst_length],
    matrix,
    start,
    lst_length,
)

# list_list_col_slice
list_list_col_slice_body = ite(
    matrix.len() < 1,
    Matrix.empty(Int),
    matrix[1:].col_slice(start, end).prepend(matrix[0][start:end]),
)
list_list_col_slice_fn_decl = fn_decl_recursive(
    "list_list_col_slice", Matrix[Int], list_list_col_slice_body, matrix, start, end
)
# list_list_col_slice_with_length
list_list_col_slice_with_length_fn_decl = fn_decl_recursive(
    "list_list_col_slice_with_length",
    Matrix[Int],
    matrix.col_slice(start, start + lst_length),
    matrix,
    start,
    lst_length,
)
# matrix transpose
firsts_body = ite(
    matrix.len() < 1,
    mlList.empty(Int),
    call("firsts", mlList[Int], matrix[1:]).prepend(matrix[0][0]),
)
firsts_fn_decl = fn_decl_recursive("firsts", mlList[Int], firsts_body, matrix)
rests_body = ite(
    matrix.len() < 1, Matrix.empty(Int), matrix.col_slice(1, matrix[0].len())
)
rests_fn_decl = fn_decl_recursive("rests", Matrix[Int], rests_body, matrix)
matrix_transpose_body = ite(
    matrix.len() < 1,
    Matrix.empty(Int),
    call("rests", Matrix[Int], matrix)
    .transpose()
    .prepend(call("firsts", mlList[Int], matrix)),
)
matrix_transpose_fn_decl = fn_decl_recursive(
    "matrix_transpose", Matrix[Int], matrix_transpose_body, matrix
)

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
