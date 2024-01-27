from metalift.ir import Call, Expr, Lit

mode = "Float"

translations = {
    "vec_elemwise_mul": lambda args: f"torch.multiply({pytorch_codegen(args[1])}, {pytorch_codegen(args[0])})",
    "matrix_vec_mul": lambda args: f"torch.matmul({pytorch_codegen(args[0])}, {pytorch_codegen(args[1])})",
    "matrix_transpose": lambda args: f"torch.transpose({pytorch_codegen(args[0])}, 0, 1)",
    "test_sqrt": lambda args: f"torch.sqrt(torch.as_tensor({pytorch_codegen(args[0])}))",
    #### Which of the name is used for sqrt?
    "integer_sqrt": lambda args: f"torch.sqrt(torch.as_tensor({pytorch_codegen(args[0])}))",
    "vec_map": lambda args: f"torch.sqrt(torch.as_tensor({pytorch_codegen(args[0])}))"
    if pytorch_codegen(args[1]) == "integer_sqrt"
    else f"torch.exp({pytorch_codegen(args[0])})",
    "reduce_sum": lambda args: f"torch.sum({pytorch_codegen(args[0])})",
    "reduce_max": lambda args: f"torch.max({pytorch_codegen(args[0])})",
    "list_length": lambda args: f"{pytorch_codegen(args[0])}.size(dim=0)",
    "vec_scalar_mul": lambda args: f"torch.multiply({pytorch_codegen(args[0])}, {pytorch_codegen(args[1])})",
    "scalar_vec_div": lambda args: f"torch.divide({pytorch_codegen(args[0])}, {pytorch_codegen(args[1])})",
    "rand": lambda args: "torch.randint(1, 2147483647, base.shape, dtype=torch.int32, device='cuda')",
    "Ite": lambda args: f"torch.where({pytorch_codegen(args[0])}, {pytorch_codegen(args[1])}, {pytorch_codegen(args[2])})",
    "Lt": lambda args: f"torch.less({pytorch_codegen(args[0])}, {pytorch_codegen(args[1])})",
    "Le": lambda args: f"torch.less_equal({pytorch_codegen(args[0])}, {pytorch_codegen(args[1])})",
    "Gt": lambda args: f"torch.greater({pytorch_codegen(args[0])}, {pytorch_codegen(args[1])})",
    "Ge": lambda args: f"torch.greater_equal({pytorch_codegen(args[0])}, {pytorch_codegen(args[1])})",
    "Eq": lambda args: f"torch.eq({pytorch_codegen(args[0])}, {pytorch_codegen(args[1])})",
    # General for any of the frameworks
    "vec_scalar_sub": lambda args: f"{pytorch_codegen(args[1])} - {pytorch_codegen(args[0])}",
    "vec_scalar_div": lambda args: f"{pytorch_codegen(args[1])} / {pytorch_codegen(args[0])}",
    "vec_scalar_add": lambda args: f"{pytorch_codegen(args[1])} + {pytorch_codegen(args[0])}",
    "scalar_vec_sub": lambda args: f"{pytorch_codegen(args[0])} - {pytorch_codegen(args[1])}",
    # General for any python code
    "list_list_col_slice_with_length": lambda args: f"{pytorch_codegen(args[0])}[:, {pytorch_codegen(args[1])}:{pytorch_codegen(args[1])} + {args[2]}]",
    "list_slice_with_length": lambda args: f"{pytorch_codegen(args[0])}[{pytorch_codegen(args[1])}:{pytorch_codegen(args[1])} + {args[2]}]",
    "list_take": lambda args: f"{pytorch_codegen(args[0])}[:{pytorch_codegen(args[1])}]",
    "Div": lambda args: f"{pytorch_codegen(args[0])} / {pytorch_codegen(args[1])}"
    if mode == "Float"
    else f"{pytorch_codegen(args[0])} // {pytorch_codegen(args[1])}",
    "Mul": lambda args: f"{pytorch_codegen(args[0])} * {pytorch_codegen(args[1])}",
    "Sub": lambda args: f"{pytorch_codegen(args[0])} - {pytorch_codegen(args[1])}",
    "Add": lambda args: f"{pytorch_codegen(args[0])} + {pytorch_codegen(args[1])}",
    "Mod": lambda args: f"{pytorch_codegen(args[0])} % {pytorch_codegen(args[1])}",
    "And": lambda args: " and ".join(pytorch_codegen(a) for a in args),
    "Or": lambda args: " or ".join(pytorch_codegen(a) for a in args),
    "Not": lambda args: f"not {pytorch_codegen(args[0])}",
}


def pytorch_codegen(expr: Expr) -> str:
    if isinstance(expr, Call):
        if expr.name() in {"nested_selection_two_args", "vec_map"}:
            return ""
        if expr.name() == "scalar_vec_div":
            import pdb

            pdb.set_trace()
        return translations[expr.name()](expr.args[1:])
    elif isinstance(expr, Lit):
        return f"{expr.val()}"
    elif expr.__class__.__name__ in translations.keys():
        return translations[expr.__class__.__name__](expr.args)
    else:
        return "%s" % (expr)
