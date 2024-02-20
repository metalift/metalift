from metalift.ir import Int, Matrix, call, fn_decl_recursive
from tenspiler.codegen.gaudi_codegen import gaudi_codegen

# def test():
#     return f"""
#         hello
#             hi
#     """
# print(textwrap.dedent(test()))
# exit(0)

base = Matrix(Int, "base")
active = Matrix(Int, "active")
fn_decl = fn_decl_recursive(
    "multiply_blend_8_ps",
    Matrix[Int],
    call(
        "matrix_scalar_div",
        Matrix[Int],
        Int(255),
        call("matrix_elemwise_mul", Matrix[Int], base, active),
    ),
    base,
    active,
)
result = gaudi_codegen(fn_decl, [])
print(result)
