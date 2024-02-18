from dataclasses import dataclass
from enum import Enum
from typing import Dict, List, Optional, Union

from metalift.ir import (
    Call,
    Expr,
    FnDecl,
    FnDeclRecursive,
    Int,
    Lit,
    ObjectT,
    Var,
    create_object,
    is_list_type,
    is_matrix_type,
)
from tests.llvm.tenspiler.codegen.utils import DataType


class CType(Enum):
    """C types"""

    INT = "int"
    FLOAT = "float"


# TODO(jie): think of a better name
class GaudiBodyType(CType):
    """Gaudi types used in the body (inside the loops). All C types are supported in the Gaudi body."""

    # 1 vector, with 256 8-bit integers
    UCHAR256 = "uchar256"
    # 1 vector, with 64 32-bit floats
    FLOAT64 = "float64"
    # 4 vectors, each with 64 32-bit integers
    UINT256 = "uint256"
    # 4 vectors, each with 64 32-bit floats
    FLOAT256 = "float256"

    @staticmethod
    def from_ir_and_data_type(ir_type: ObjectT, d_type: DataType) -> "GaudiBodyType":
        if ir_type is Int:
            if d_type == DataType.INT:
                return CType.INT
            else:
                return CType.FLOAT
        elif is_list_type(ir_type) or is_matrix_type(ir_type):
            if d_type == DataType.INT:
                return GaudiBodyType.UCHAR256
            else:
                return GaudiBodyType.FLOAT64
        else:
            raise Exception(
                f"Unsupported Gaudi type for ir type {ir_type} and data type {d_type}"
            )


class GaudiHeaderType(CType):
    """Types used Gaudi's function header."""

    TENSOR = "tensor"

    @staticmethod
    def from_ir_and_data_type(ir_type: ObjectT, d_type: DataType) -> "GaudiHeaderType":
        if is_list_type(ir_type) or is_matrix_type(ir_type):
            return GaudiHeaderType.TENSOR
        elif (
            ir_type is Int
        ):  # TODO(jie): double check if you can compare types like this
            if d_type == DataType.FLOAT:
                return GaudiHeaderType.FLOAT
            else:
                return GaudiHeaderType.INT
        else:
            raise Exception(f"Unsupported Gaudi type {ty}")


@dataclass(kw_only=True)
class GaudiInstr:
    dest_name: Optional[str]
    dest_type: Optional[GaudiBodyType]
    instr_str: str


def gaudi_codegen(
    ps_fn_decl: Union[FnDecl, FnDeclRecursive],
    all_synthesized_fns: Dict[str, Union[FnDecl, FnDeclRecursive]],
    override_arg_types: Dict[str, GaudiHeaderType] = {},
    d_type: DataType = DataType.UINT8,
) -> str:
    def expr_codegen(
        expr: Expr,
        instructions: List[GaudiInstr],
        scalar_override_type: Optional[
            GaudiBodyType
        ] = None,  # If we want to broadcast a scalar
    ) -> None:
        # Helper functions
        def get_gaudi_body_type(ir_type: ObjectT) -> GaudiBodyType:
            """Given the IR type, and the data type, returns the Gaudi type used in the body. Namely, when data type is float, all integers are converted to float."""
            if scalar_override_type is not None:
                return scalar_override_type
            else:
                return GaudiBodyType.from_ir_and_data_type(ir_type, d_type)

        def format_instruction(expr: str, gaudi_body_type: GaudiBodyType) -> str:
            """Formats the instruction with the destination name and type."""
            return f"{gaudi_body_type.value} v{len(instructions)} = {expr};"

        def convert_arg(
            arg_name: str,
            arg_gaudi_type: GaudiBodyType,
            expected_gaudi_type: GaudiBodyType,
        ) -> GaudiInstr:
            """Converts the argument to the expected type. Returns the metadata of the new argument. Additionally, adds the instruction to the list of instructions."""
            convert_instr_name = (
                f"convert_{arg_gaudi_type.value}_to_{expected_gaudi_type.value}"
            )
            convert_instr = format_instruction(
                f"{convert_instr_name}({arg_name})", expected_gaudi_type
            )
            new_arg_name = f"v{len(instructions)}"
            new_metadata = GaudiInstr(
                dest_name=new_arg_name,
                dest_type=expected_gaudi_type,
                instr=convert_instr,
            )
            instructions.append(new_metadata)
            return new_metadata

        # Generate the instructions for the body
        if isinstance(expr, Var):
            if is_list_type(expr.type) or is_matrix_type(expr.type):
                if d_type == DataType.FLOAT:
                    instr_name = f"v_f32_ld_tnsr_b"
                    instr_gaudi_type = GaudiBodyType.FLOAT64
                else:
                    instr_name = f"v_u8_ld_tnsr_b"
                    instr_gaudi_type = GaudiBodyType.UCHAR256
                instr = GaudiInstr(
                    dest_name=f"v{len(instructions)}",
                    dest_type=instr_gaudi_type,
                    instr=format_instruction(
                        f"{instr_name}(inputCoord, {expr.name()}", instr_gaudi_type
                    ),
                )
                instructions.append(instr)
                return
            else:
                instr_gaudi_type = get_gaudi_body_type(expr.type)
                instr = GaudiInstr(
                    dest_name=f"v{len(instructions)}",
                    dest_type=instr_gaudi_type,
                    instr=format_instruction(expr.name(), instr_gaudi_type),
                )
                instructions.append(instr)
                return
        elif isinstance(expr, Lit):
            instr_gaudi_type = get_gaudi_body_type(expr.type)
            instr = GaudiInstr(
                dest_name=f"v{len(instructions)}",
                dest_type=instr_gaudi_type,
                instr=format_instruction(expr.name(), instr_gaudi_type),
            )
            instructions.append(instr)
            return
        elif isinstance(expr, Call):
            fn_name = expr.name()

            # Group function names
            add_fn_names = {
                "matrix_elemwise_add",
                "vec_elemwise_add",
                "matrix_scalar_add",
                "vec_scalar_add",
            }
            sub_fn_names = {
                "matrix_elemwise_sub",
                "vec_elemwise_sub",
                "matrix_scalar_sub",
                "vec_scalar_sub",
                "scalar_matrix_sub",
                "scalar_vec_sub",
            }
            mul_fn_names = {
                "matrix_elemwise_mul",
                "vec_elemwise_mul",
                "matrix_scalar_mul",
                "vec_scalar_mul",
            }
            div_fn_names = {
                "matrix_elemwise_div",
                "vec_elemwise_div",
                "matrix_scalar_div",
                "vec_scalar_div",
                "scalar_matrix_div",
                "scalar_vec_div",
            }
            if fn_name in div_fn_names:
                if d_type == DataType.INT:
                    if "scalar" in fn_name:
                        # Since we need to convert everything to float anyways, we just broadcast
                        # the scalar as a float from the beginning
                        expr_codegen(
                            expr.arguments()[0],
                            instructions,
                            scalar_override_type=GaudiBodyType.FLOAT64,
                        )
                        first_arg_metadata = instructions[-1]
                        expr_codegen(expr.arguments()[1], instructions)
                        second_arg_metadata = instructions[-1]
                    else:
                        expr_codegen(expr.arguments()[0], instructions)
                        first_arg_metadata = instructions[-1]
                        expr_codegen(expr.arguments()[1], instructions)
                        second_arg_metadata = instructions[-1]

                    if fn_name.startswith("scalar"):
                        first_arg_metadata, second_arg_metadata = (
                            second_arg_metadata,
                            first_arg_metadata,
                        )

                    # We need to convert all the uchar256/uint256 to float256
                    if first_arg_metadata.dest_type != GaudiBodyType.FLOAT256:
                        first_arg_metadata = convert_arg(
                            first_arg_metadata.dest_name,
                            first_arg_metadata.dest_type,
                            GaudiBodyType.FLOAT256,
                        )
                    if second_arg_metadata.dest_type != GaudiBodyType.FLOAT256:
                        second_arg_metadata = convert_arg(
                            second_arg_metadata.dest_name,
                            second_arg_metadata.dest_type,
                            GaudiBodyType.FLOAT256,
                        )

                    # Now we both args are of type float256
                    result_arg_name = f"v{len(instructions)}"
                    declaration_instr_metadata = GaudiInstr(
                        dest_name=result_arg_name,
                        dest_type=GaudiBodyType.FLOAT256,
                        instr=f"{GaudiBodyType.FLOAT256.value} {result_arg_name};",
                    )
                    instructions.append(declaration_instr_metadata)
                    # TODO(jie): whether the variables here are actually used.
                    first_arg_name = first_arg_metadata.dest_name
                    second_arg_name = second_arg_metadata.dest_name
                    v1_instr_metadata = GaudiInstr(
                        dest_name=None,
                        dest_type=None,
                        instr=f"{result_arg_name}.v1 = v_f32_mul_b({first_arg_name}.v1, {second_arg_name}.v1);",
                    )
                    v2_instr_metadata = GaudiInstr(
                        dest_name=None,
                        dest_type=None,
                        instr=f"{result_arg_name}.v2 = v_f32_mul_b({first_arg_name}.v2, {second_arg_name}.v2);",
                    )
                    v3_instr_metadata = GaudiInstr(
                        dest_name=None,
                        dest_type=None,
                        instr=f"{result_arg_name}.v3 = v_f32_mul_b({first_arg_name}.v3, {second_arg_name}.v3);",
                    )
                    v4_instr_metadata = GaudiInstr(
                        dest_name=None,
                        dest_type=None,
                        instr=f"{result_arg_name}.v4 = v_f32_mul_b({first_arg_name}.v4, {second_arg_name}.v4);",
                    )
                    instructions.extend(
                        [
                            v1_instr_metadata,
                            v2_instr_metadata,
                            v3_instr_metadata,
                            v4_instr_metadata,
                        ]
                    )

                    # Last, we convert this float256 to uchar256
                    convert_arg(
                        result_arg_name, GaudiBodyType.FLOAT256, GaudiBodyType.UCHAR256
                    )
                    return
                else:
                    # Data type is float.
                    if "scalar" in fn_name:
                        # If it's a scalar operation, then we need to broadcast the scalar
                        expr_codegen(
                            expr.arguments()[0],
                            instructions,
                            scalar_override_type=GaudiBodyType.FLOAT64,
                        )
                        first_arg_metadata = instructions[-1]
                        expr_codegen(expr.arguments()[1], instructions)
                        second_arg_metadata = instructions[-1]
                    else:
                        expr_codegen(expr.arguments()[0], instructions)
                        first_arg_metadata = instructions[-1]
                        expr_codegen(expr.arguments()[1], instructions)
                        second_arg_metadata = instructions[-1]

                    if fn_name.startswith("scalar"):
                        first_arg_metadata, second_arg_metadata = (
                            second_arg_metadata,
                            first_arg_metadata,
                        )

                    # Convert arguments to the correct types
                    if first_arg_metadata.dest_type != GaudiBodyType.FLOAT64:
                        first_arg_metadata = convert_arg(
                            first_arg_metadata.dest_name,
                            first_arg_metadata.dest_type,
                            GaudiBodyType.FLOAT64,
                        )
                    if second_arg_metadata.dest_type != GaudiBodyType.FLOAT64:
                        second_arg_metadata = convert_arg(
                            second_arg_metadata.dest_name,
                            second_arg_metadata.dest_type,
                            GaudiBodyType.FLOAT64,
                        )

                    reciprocal_instr_name = "v_reciprocal_fast_f32"
                    reciprocal_instr = format_instruction(
                        f"{reciprocal_instr_name}({second_arg_metadata.dest_name})",
                        GaudiBodyType.FLOAT64,
                    )
                    reciprocal_arg_name = f"v{len(instructions)}"
                    reciprocal_instr_metadata = GaudiInstr(
                        dest_name=reciprocal_arg_name,
                        dest_type=GaudiBodyType.FLOAT64,
                        instr=reciprocal_instr,
                    )
                    instructions.append(reciprocal_instr_metadata)

                    # Now we multiply the first arg by the reciprocal of the second arg
                    reciprocal_mul_instr = GaudiInstr(
                        dest_name=f"v{len(instructions)}",
                        dest_type=GaudiBodyType.FLOAT64,
                        instr=format_instruction(
                            f"v_f32_mul_b({first_arg_metadata.dest_name}, {reciprocal_arg_name})",
                            GaudiBodyType.FLOAT64,
                        ),
                    )
                    instructions.append(reciprocal_mul_instr)
                    return

            if fn_name in {*add_fn_names, *sub_fn_names, *mul_fn_names}:
                if d_type == DataType.INT:
                    expected_arg_type = GaudiBodyType.UCHAR256
                    if fn_name in add_fn_names:
                        instr_name = f"v_u8_add_b"
                        ret_gaudi_type = GaudiBodyType.UCHAR256
                    elif fn_name in sub_fn_names:
                        instr_name = f"v_u8_sub_b"
                        ret_gaudi_type = GaudiBodyType.UCHAR256
                    else:
                        instr_name = f"v_u8_mul_b"
                        ret_gaudi_type = GaudiBodyType.UINT256
                else:
                    expected_arg_type = GaudiBodyType.FLOAT64
                    if fn_name in add_fn_names:
                        instr_name = f"v_f32_add_b"
                        ret_gaudi_type = GaudiBodyType.FLOAT64
                    elif fn_name in sub_fn_names:
                        instr_name = f"v_f32_sub_b"
                        ret_gaudi_type = GaudiBodyType.FLOAT64
                    else:
                        instr_name = f"v_f32_mul_b"
                        ret_gaudi_type = GaudiBodyType.FLOAT64

                if "scalar" in fn_name:
                    # If it's a scalar operation, then we need to broadcast the scalar
                    expr_codegen(
                        expr.arguments()[0],
                        instructions,
                        scalar_override_type=expected_arg_type,
                    )
                    first_arg_metadata = instructions[-1]
                    expr_codegen(expr.arguments()[1], instructions)
                    second_arg_metadata = instructions[-1]
                else:
                    expr_codegen(expr.arguments()[0], instructions)
                    first_arg_metadata = instructions[-1]
                    expr_codegen(expr.arguments()[1], instructions)
                    second_arg_metadata = instructions[-1]

                if fn_name.startswith("scalar"):
                    first_arg_metadata, second_arg_metadata = (
                        second_arg_metadata,
                        first_arg_metadata,
                    )

                if first_arg_metadata.dest_type != expected_arg_type:
                    first_arg_metadata = convert_arg(
                        first_arg_metadata.dest_name,
                        first_arg_metadata.dest_type,
                        expected_arg_type,
                    )
                if second_arg_metadata.dest_type != expected_arg_type:
                    second_arg_metadata = convert_arg(
                        second_arg_metadata.dest_name,
                        second_arg_metadata.dest_type,
                        expected_arg_type,
                    )

                instr = GaudiInstr(
                    dest_name=f"v{len(instructions)}",
                    dest_type=ret_gaudi_type,
                    instr=format_instruction(
                        f"{instr_name}({first_arg_metadata.dest_name}, {second_arg_metadata.dest_name})",
                        ret_gaudi_type,
                    ),
                )
                instructions.append(instr)
                return

    ###############################
    # Begins actual code generation
    ###############################

    # TPC-C only supports vec-vec/matrix-matrix element-wise or vec-scalar/matrix-scalar
    # operations, which means the final return value has to either be a vector or a matrix.
    is_return_type_vec = is_list_type(ps_fn_decl.returnT())
    is_return_type_matrix = is_matrix_type(ps_fn_decl.returnT())
    if not is_return_type_vec and not is_return_type_matrix:
        raise Exception("Can only return a tensor from a TPC-C function!")

    # First we generate the function header. We include the tensor to return in the arguments,
    # and it should always be the last argument.
    rv_name = f"{ps_fn_decl.name()}_rv"
    rv = create_object(ps_fn_decl.returnT(), rv_name).src
    arguments = [
        f"{GaudiHeaderType.from_ir_and_data_type(arg.type, d_type).value} {arg.name()}"
        for arg in [*ps_fn_decl.arguments(), rv]
    ]
    arguments_str = ", ".join(arguments)
    header = f"void main({arguments_str})"

    # If mode is float, then we operate on 64 elements at a time, else 256
    if d_type == DataType.FLOAT:
        vec_len = 64
        store_instr = "v_f32_st_tnsr"
    else:
        vec_len = 256
        store_instr = "v_u8_st_tnsr"

    # Generate the returned expression
    instructions: List[GaudiInstr] = []
    expr_codegen(ps_fn_decl.body(), instructions)
    instr_strs = "\n".join([instr.instr_str for instr in instructions])

    # Assign the last variable to the return value
    ret_expr = instructions[-1].dest_name

    if is_return_type_vec:
        body = f"""
        int5 index_space_start = get_index_space_offset();
        int5 index_space_end = index_space_start + get_index_space_size();

        int5 inputCoord = {{ 0 }};
        int5 outputCoord = {{ 0 }};

        unsigned vec_len = {vec_len};

        #pragma loop_unroll(8)
        for(int i = index_space_start[0]; i < index_space_end[0]; i++) {{
            // index space mapping
            inputCoord[0] = outputCoord[0] = (i * vec_len);
            {instr_strs}
            {store_instr}(outputCoord, {rv_name}, {ret_expr});
        }}
        """
    else:
        # matrix return type
        body = f"""
        int5 index_space_start = get_index_space_offset();
        int5 index_space_end = index_space_start + get_index_space_size();

        int5 inputCoord = {{ 0 }};
        int5 outputCoord = {{ 0 }};

        unsigned vec_len = {vec_len};

        for(int i = index_space_start[0]; i < index_space_end[0]; i++) {{
            #pragma loop_unroll(4)
            for (int j = index_space_start[1]; j < index_space_end[1]; j++) {{
                // index space mapping
                // coordinate 0 is for dim0.
                inputCoord[0] = outputCoord[0] = (i * vec_len);
                // coordinate 1 is for dim1.
                inputCoord[1] = outputCoord[1] = j;

                {store_instr}(outputCoord, {rv_name}, {ret_expr});
            }}
        }}
        """

    return f"""
    {header} {{
        {body}
    }}
    """
