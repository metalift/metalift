import textwrap
from dataclasses import dataclass
from enum import Enum
from typing import Dict, List, Optional, Union

from metalift.ir import (
    Add,
    Call,
    Div,
    Eq,
    Expr,
    FnDecl,
    FnDeclRecursive,
    Ge,
    Gt,
    Int,
    Le,
    Lit,
    Lt,
    Matrix,
    Mul,
    ObjectT,
    Sub,
    Var,
    call,
    create_object,
    is_list_type,
    is_matrix_type,
)
from tenspiler.codegen.utils import DataType

# Indentation is 4 spaces
INDENTATION = " " * 4


class CType(Enum):
    """C types"""

    UINT8 = "uint8_t"
    FLOAT = "float"

    @property
    def is_primitive(self) -> bool:
        return True


# TODO(jie): think of a better name
class GaudiBodyType(CType, Enum):
    """Gaudi types used in the body (inside the loops). All C types are supported in the Gaudi body."""

    # 1 vector, with 256 8-bit integers
    UCHAR256 = "uchar256"
    # 1 vector, with 64 32-bit floats
    FLOAT64 = "float64"
    # 4 vectors, each with 64 32-bit integers
    UINT256 = "uint256"
    # 4 vectors, each with 64 32-bit floats
    FLOAT256 = "float256"

    @property
    def is_primitive(self) -> bool:
        return self in {GaudiBodyType.UINT8, GaudiBodyType.FLOAT}

    @staticmethod
    def from_ir_and_data_type(ir_type: ObjectT, d_type: DataType) -> "GaudiBodyType":
        if ir_type is Int:
            if d_type == DataType.INT:
                return GaudiBodyType.UINT8
            else:
                return GaudiBodyType.FLOAT
        elif is_list_type(ir_type) or is_matrix_type(ir_type):
            if d_type is DataType.INT:
                return GaudiBodyType.UCHAR256
            else:
                return GaudiBodyType.FLOAT64
        else:
            raise Exception(
                f"Unsupported Gaudi type for ir type {ir_type} and data type {d_type}"
            )


class GaudiHeaderType(CType, Enum):
    """Types used Gaudi's function header."""

    TENSOR = "tensor"

    @staticmethod
    def from_ir_and_data_type(ir_type: ObjectT, d_type: DataType) -> "GaudiHeaderType":
        if is_list_type(ir_type) or is_matrix_type(ir_type):
            return GaudiHeaderType.TENSOR
        elif ir_type is Int:
            if d_type == DataType.FLOAT:
                return GaudiHeaderType.FLOAT
            else:
                return GaudiHeaderType.UINT8
        else:
            raise Exception(
                f"Cannot infer Gaudi type from ir type {ir_type} and data type {d_type}"
            )


@dataclass
class GaudiInstr:
    dest_name: Optional[str]
    dest_type: Optional[GaudiBodyType]
    expr_str: Optional[str]


def gaudi_codegen(
    ps_fn_decl: Union[FnDecl, FnDeclRecursive],
    all_synthesized_fns: Dict[str, Union[FnDecl, FnDeclRecursive]],
    override_arg_types: Dict[str, GaudiHeaderType] = {},
    d_type: DataType = DataType.INT,
) -> str:
    def expr_codegen(
        expr: Expr,
        *,
        override_type: Optional[GaudiBodyType] = None,  # Type to override
        vars_to_replace: Dict[str, Expr] = {},
    ) -> None:
        # Helper functions
        def get_gaudi_body_type_with_override(ir_type: ObjectT) -> GaudiBodyType:
            """Given the IR type, and the data type, returns the Gaudi type used in the body. Namely, when data type is float, all integers are converted to float."""
            return override_type or get_gaudi_body_type(ir_type)

        def get_gaudi_body_type(ir_type: ObjectT) -> GaudiBodyType:
            """Given the IR type, and the data type, returns the Gaudi type used in the body. Namely, when data type is float, all integers are converted to float."""
            return GaudiBodyType.from_ir_and_data_type(ir_type, d_type)

        def format_gaudi_instr(
            expr_str: Optional[str],
            gaudi_body_type: GaudiBodyType,
            ignore_dest: bool = False,
        ) -> GaudiInstr:
            # TODO(jie): change this description
            """Formats the instruction with the destination name and type."""
            if ignore_dest:
                dest_name = None
            else:
                dest_name = f"v{len(instructions)}"
            gaudi_instr = GaudiInstr(dest_name, gaudi_body_type, expr_str)
            instructions.append(gaudi_instr)
            return gaudi_instr

        def convert_arg(
            arg_name: str,
            arg_gaudi_type: GaudiBodyType,
            expected_gaudi_type: GaudiBodyType,
        ) -> Optional[GaudiInstr]:
            """Converts the argument to the expected type. Returns the metadata of the new argument. Additionally, adds the instruction to the list of instructions."""
            if arg_gaudi_type == expected_gaudi_type:
                return None
            non_default_switches = {
                (GaudiBodyType.UINT256, GaudiBodyType.FLOAT256): "SW_LINEAR",
                (GaudiBodyType.FLOAT256, GaudiBodyType.UCHAR256): "SW_RD",
            }
            convert_instr_name = (
                f"convert_{arg_gaudi_type.value}_to_{expected_gaudi_type.value}"
            )
            # By default, we use the 0 switch
            switch = non_default_switches.get((arg_gaudi_type, expected_gaudi_type), 0)
            return format_gaudi_instr(
                f"{convert_instr_name}({arg_name}, {switch})", expected_gaudi_type
            )

        fn_dtype = "f32" if d_type == DataType.FLOAT else "u8"
        default_expr_type = get_gaudi_body_type(expr.type)
        final_expr_type = get_gaudi_body_type_with_override(expr.type)

        expr_instr: Optional[GaudiInstr] = None

        # Generate the instructions for the body
        if isinstance(expr, Var):
            if expr.name() in vars_to_replace:
                return expr_codegen(
                    vars_to_replace[expr.name()],
                    override_type=override_type,
                    vars_to_replace=vars_to_replace,
                )
            if is_list_type(expr.type) or is_matrix_type(expr.type):
                expr_str = f"v_{fn_dtype}_ld_tnsr_b(inputCoord, {expr.name()})"
            else:
                expr_str = expr.name()
            expr_instr = format_gaudi_instr(expr_str, default_expr_type)
            return (
                convert_arg(expr_instr.dest_name, default_expr_type, final_expr_type)
                or expr_instr
            )
        elif isinstance(expr, Lit):
            expr_instr = format_gaudi_instr(str(expr.val()), default_expr_type)
            return (
                convert_arg(expr_instr.dest_name, default_expr_type, final_expr_type)
                or expr_instr
            )
        elif any(isinstance(expr, cls) for cls in [Add, Sub, Mul, Div]):
            if default_expr_type.is_primitive:
                if isinstance(expr, Add):
                    op = "+"
                elif isinstance(expr, Sub):
                    op = "-"
                elif isinstance(expr, Mul):
                    op = "*"
                else:
                    op = "/"
                first_arg_instr = expr_codegen(
                    expr.args[0],
                    vars_to_replace=vars_to_replace,
                )
                second_arg_instr = expr_codegen(
                    expr.args[1],
                    vars_to_replace=vars_to_replace,
                )
                expr_instr = format_gaudi_instr(
                    f"{first_arg_instr.dest_name} {op} {second_arg_instr.dest_name}",
                    default_expr_type,
                )
                return (
                    convert_arg(
                        expr_instr.dest_name, default_expr_type, final_expr_type
                    )
                    or expr_instr
                )
            else:
                if isinstance(expr, Add):
                    fn_name = "matrix_elemwise_add"
                elif isinstance(expr, Sub):
                    fn_name = "matrix_elemwise_sub"
                elif isinstance(expr, Mul):
                    fn_name = "matrix_elemwise_mul"
                else:
                    fn_name = "matrix_elemwise_div"
                return expr_codegen(
                    call(fn_name, Matrix[Int], *expr.args).src,
                    override_type=default_expr_type,
                    vars_to_replace=vars_to_replace,
                )

        elif isinstance(expr, Call):
            fn_name = expr.name()

            # Handle select function
            if fn_name.endswith("matrix_selection_two_args"):
                for name, fn in all_synthesized_fns.items():
                    if name.endswith("select_two_args"):
                        select_two_args_fn_decl = fn
                if select_two_args_fn_decl is None:
                    raise ValueError("select_two_args not found")
                select_two_args_body = select_two_args_fn_decl.body()
                cond = select_two_args_body.c()
                if_then = select_two_args_body.e1()
                if_else = select_two_args_body.e2()
                select_args = select_two_args_fn_decl.arguments()[:2]
                matrix_args = expr.arguments()[:2]
                vars_to_replace: Dict[str, Expr] = {}
                for i in range(2):
                    vars_to_replace[select_args[i].name()] = matrix_args[i]
                if isinstance(cond, Gt):
                    cond_instr_name = f"v_{fn_dtype}_sel_grt_{fn_dtype}_b"
                elif isinstance(cond, Eq):
                    cond_instr_name = f"v_{fn_dtype}_sel_eq_{fn_dtype}_b"
                elif isinstance(cond, Lt):
                    cond_instr_name = f"v_{fn_dtype}_sel_less_{fn_dtype}_b"
                elif isinstance(cond, Le):
                    cond_instr_name = f"v_{fn_dtype}_sel_leq_{fn_dtype}_b"
                elif isinstance(cond, Ge):
                    cond_instr_name = f"v_{fn_dtype}_sel_geq_{fn_dtype}_b"
                else:
                    raise Exception(f"Unsupported condition {cond} for select_two_args")

                cond_arg0_instr = expr_codegen(
                    cond.args[0],
                    override_type=default_expr_type,
                    vars_to_replace=vars_to_replace,
                )
                cond_arg1_instr = expr_codegen(
                    cond.args[1],
                    override_type=default_expr_type,
                    vars_to_replace=vars_to_replace,
                )
                if_then_instr = expr_codegen(
                    if_then,
                    override_type=default_expr_type,
                    vars_to_replace=vars_to_replace,
                )
                if_else_instr = expr_codegen(
                    if_else,
                    override_type=default_expr_type,
                    vars_to_replace=vars_to_replace,
                )
                if_else_instr = instructions[-1]
                expr_str = f"{cond_instr_name}({cond_arg0_instr.dest_name}, {cond_arg1_instr.dest_name}, {if_then_instr.dest_name}, {if_else_instr.dest_name})"
                expr_instr = format_gaudi_instr(expr_str, default_expr_type)
                return (
                    convert_arg(
                        expr_instr.dest_name, default_expr_type, final_expr_type
                    )
                    or expr_instr
                )

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
                    expected_arg_type = GaudiBodyType.FLOAT256
                else:
                    expected_arg_type = GaudiBodyType.FLOAT64

                if "scalar" in fn_name:
                    # Since we need to convert everything to float anyways, we just broadcast
                    # the scalar as a float from the beginning
                    first_arg_instr = expr_codegen(
                        expr.arguments()[0],
                        override_type=GaudiBodyType.FLOAT64,
                        vars_to_replace=vars_to_replace,
                    )
                else:
                    first_arg_instr = expr_codegen(
                        expr.arguments()[0],
                        override_type=expected_arg_type,
                        vars_to_replace=vars_to_replace,
                    )
                    second_arg_instr = expr_codegen(
                        expr.arguments()[1],
                        override_type=expected_arg_type,
                        vars_to_replace=vars_to_replace,
                    )
                if fn_name.startswith("scalar"):
                    first_arg_instr, second_arg_instr = (
                        second_arg_instr,
                        first_arg_instr,
                    )

                # Now get fields to multiply
                if first_arg_instr.dest_type == GaudiBodyType.FLOAT64:
                    first_arg_mult_lst = [first_arg_instr.dest_name]
                else:
                    first_arg_mult_lst = [
                        f"{first_arg_instr.dest_name}.v{i}" for i in range(1, 5)
                    ]

                # Now get the reciprocal of the second argument
                if second_arg_instr.dest_type == GaudiBodyType.FLOAT64:
                    reciprocal_instr = format_gaudi_instr(
                        f"v_reciprocal_fast_f32({second_arg_instr.dest_name})",
                        GaudiBodyType.FLOAT64,
                    )
                    second_arg_mult_lst = [reciprocal_instr.dest_name]
                else:
                    # second arg is of type float256. We need to call v_reciprocal_fast_f32
                    # on each of the fields.
                    second_arg_mult_lst = [
                        f"v_reciprocal_fast_f32({second_arg_instr.dest_name}.v{i})"
                        for i in range(1, 5)
                    ]

                # Now we both args are of type float256 or float64.
                result_instr = format_gaudi_instr(
                    expr_str=None, gaudi_body_type=GaudiBodyType.FLOAT256
                )
                result_arg_name = result_instr.dest_name

                if len(first_arg_mult_lst) == 1 and len(second_arg_mult_lst) == 1:
                    format_gaudi_instr(
                        f"v_f32_mul_b({first_arg_mult_lst[0]}, {second_arg_mult_lst[0]})",
                        GaudiBodyType.FLOAT64,
                    )
                else:
                    for i in range(1, 5):
                        if len(first_arg_mult_lst) == 1:
                            first_arg_mult = first_arg_mult_lst[0]
                        else:
                            first_arg_mult = first_arg_mult_lst[i - 1]

                        if len(second_arg_mult_lst) == 1:
                            second_arg_mult = second_arg_mult_lst[0]
                        else:
                            second_arg_mult = second_arg_mult_lst[i - 1]

                        format_gaudi_instr(
                            expr_str=f"{result_arg_name}.v{i} = v_f32_mul_b({first_arg_mult}, {second_arg_mult});",
                            gaudi_body_type=GaudiBodyType.FLOAT64,
                            ignore_dest=True,
                        )
                # Last, we convert this float256 to uchar256
                return (
                    convert_arg(
                        result_arg_name, GaudiBodyType.FLOAT256, GaudiBodyType.UCHAR256
                    )
                    or result_instr
                )

            if fn_name in {*add_fn_names, *sub_fn_names, *mul_fn_names}:
                ret_gaudi_type = get_gaudi_body_type(expr.type)
                expected_arg_type = get_gaudi_body_type(expr.type)
                if fn_name in add_fn_names:
                    instr_name = f"v_{fn_dtype}_add_b"
                elif fn_name in sub_fn_names:
                    instr_name = f"v_{fn_dtype}_sub_b"
                else:
                    instr_name = f"v_{fn_dtype}_mul_b"
                    if d_type == DataType.INT:
                        ret_gaudi_type = GaudiBodyType.UINT256

                first_arg_instr = expr_codegen(
                    expr.arguments()[0],
                    override_type=expected_arg_type,
                    vars_to_replace=vars_to_replace,
                )
                second_arg_instr = expr_codegen(
                    expr.arguments()[1],
                    override_type=expected_arg_type,
                    vars_to_replace=vars_to_replace,
                )

                if fn_name.startswith("scalar"):
                    first_arg_instr, second_arg_instr = (
                        second_arg_instr,
                        first_arg_instr,
                    )

                expr_instr = format_gaudi_instr(
                    f"{instr_name}({first_arg_instr.dest_name}, {second_arg_instr.dest_name})",
                    ret_gaudi_type,
                )
                return (
                    convert_arg(expr_instr.dest_name, ret_gaudi_type, final_expr_type)
                    or expr_instr
                )

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
    expr_codegen(ps_fn_decl.body())
    instr_strs = [instr.expr_str for instr in instructions]

    # Assign the last variable to the return value
    ret_expr = instructions[-1].dest_name

    if is_return_type_vec and not is_return_type_matrix:
        joined_instr_str = "\n".join(
            [instr_strs[0]]
            + [
                textwrap.indent(instr_str, INDENTATION * 3)
                for instr_str in instr_strs[1:]
            ]
        )
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
            {joined_instr_str}
            {store_instr}(outputCoord, {rv_name}, {ret_expr});
        }}
        """
        body = textwrap.dedent(body)
    else:
        joined_instr_str = "\n".join(
            [instr_strs[0]]
            + [
                textwrap.indent(instr_str, INDENTATION * 4)
                for instr_str in instr_strs[1:]
            ]
        )
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

                {joined_instr_str}

                {store_instr}(outputCoord, {rv_name}, {ret_expr});
            }}
        }}
        """
        body = textwrap.dedent(body)

    header_and_body = f"""
    {header} {{
        {textwrap.indent(body, INDENTATION * 2)}
    }}
    """
    header_and_body = textwrap.dedent(header_and_body)

    return header_and_body
