from metalift.ir import Call, Div, Expr, Int

# square(a_row, squared_buf)
# mean(squared_buf, mean_buf)
# rsqrt(mean_buf, rsqrt_buf)
# col_multiply(a_row, rsqrt_buf, scaled_buf)
# row_multiply(scaled_buf, g_tensor, out_row_buf)


def nki_codegen(expr: Expr) -> str:
    if isinstance(expr, Call):
        if expr.name() == "vec_elemwise_mul":
            args = expr.arguments()
            if args[0] == args[1]:
                return f"square({nki_codegen(args[0])})"
            else:
                raise ValueError(f"Unsupported {expr.name()} expression: {expr}")
    elif isinstance(expr, Div):
        args = expr.arguments()
        if (
            args[0] == Int(1).src
            and isinstance(args[1], Call)
            and args[1].name() == "integer_sqrt"
        ):
            sqrt_arg = args[1].arguments()[0]
            return f"rsqrt({nki_codegen(sqrt_arg)})"
        else:
            raise ValueError(f"Unsupported div expression: {expr}")
