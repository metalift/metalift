from metalift.ir import Int, List, Matrix, call, fn_decl_recursive
from tenspiler.codegen.gaudi_codegen import gaudi_codegen
from tenspiler.codegen.utils import DataType

base_matrix = Matrix(Int, "base")
active_matrix = Matrix(Int, "active")
base_vec = List(Int, "base")
active_vec = List(Int, "active")
opacity = Int("opacity")


def codegen(func):
    def wrapper(codegen_func):
        # Execute the original function
        fn_decl = func(codegen_func)

        # Post-processing code
        codegen_result = codegen_func(fn_decl, [], d_type=DataType.INT)
        print(codegen_result)

    return wrapper


@codegen
def normal_blend_8(codegen_func):
    fn_decl = fn_decl_recursive(
        "normal_blend_8_ps",
        List[Int],
        call(
            "vec_elemwise_add",
            List[Int],
            call("vec_scalar_mul", List[Int], opacity, active_vec),
            call("vec_scalar_mul", List[Int], 255 - opacity, base_vec),
        ),
        base_vec,
        active_vec,
        opacity,
    )
    return fn_decl


# def multiply_blend_8():
#     fn_decl = fn_decl_recursive(
#         "multiply_blend_8_ps",
#         Matrix[Int],
#         call(
#             "matrix_scalar_div",
#             Matrix[Int],
#             Int(255),
#             call("matrix_elemwise_mul", Matrix[Int], base_matrix, active_matrix),
#         ),
#         base_matrix,
#         active_matrix,
#         opacity
#     )
#     result = codegen(fn_decl, [], d_type=DataType.INT)
#     print(result)

normal_blend_8(gaudi_codegen)
