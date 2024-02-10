from typing import Dict

from metalift.ir import Call, Expr, Lit


def tensorflow_codegen(
    ps_expr: Expr, all_synthesized_fns: Dict[str, Expr], mode: str = "Float"
) -> str:
    translations = {
        "vec_elemwise_mul": lambda args: f"tf.multiply({helper(args[1])}, {helper(args[0])})",
        "matrix_vec_mul": lambda args: f"tf.linalg.matvec({helper(args[0])}, {helper(args[1])})",
        "matrix_transpose": lambda args: f"tf.transpose({helper(args[0])})",
        "test_sqrt": lambda args: f"tf.sqrt({helper(args[0])})",
        #### Which of the name is used for sqrt?
        "integer_sqrt": lambda args: f"torch.sqrt({helper(args[0])})",
        "vec_map": lambda args: f"torch.sqrt(torch.as_tensor({helper(args[0])}))"
        if helper(args[1]) == "integer_sqrt"
        else f"torch.exp({helper(args[0])})",
        "reduce_sum": lambda args: f"tf.reduce_sum({helper(args[0])})",
        "reduce_max": lambda args: f"torch.max({helper(args[0])})",
        "list_length": lambda args: f"{helper(args[0])}.size(dim=0)",
        "vec_scalar_mul": lambda args: f"tf.multiply({helper(args[0])}, {helper(args[1])})",
        "scalar_vec_div": lambda args: f"torch.divide({helper(args[0])}, {helper(args[1])})",
        "rand": lambda args: "torch.randint(1, 2147483647, base.shape, dtype=torch.int32, device='cuda')",
        "Ite": lambda args: f"torch.where({helper(args[0])}, {helper(args[1])}, {helper(args[2])})",
        "Lt": lambda args: f"torch.less({helper(args[0])}, {helper(args[1])})",
        "Le": lambda args: f"torch.less_equal({helper(args[0])}, {helper(args[1])})",
        "Gt": lambda args: f"torch.greater({helper(args[0])}, {helper(args[1])})",
        "Ge": lambda args: f"torch.greater_equal({helper(args[0])}, {helper(args[1])})",
        "Eq": lambda args: f"torch.eq({helper(args[0])}, {helper(args[1])})",
        # General for any of the frameworks
        "vec_scalar_sub": lambda args: f"{helper(args[1])} - {helper(args[0])}",
        "vec_scalar_div": lambda args: f"{helper(args[1])} / {helper(args[0])}",
        "vec_scalar_add": lambda args: f"{helper(args[1])} + {helper(args[0])}",
        "scalar_vec_sub": lambda args: f"{helper(args[0])} - {helper(args[1])}",
        # General for any python code
        "list_list_col_slice_with_length": lambda args: f"{helper(args[0])}[:, {helper(args[1])}:{helper(args[1])} + {args[2]}]",
        "list_slice_with_length": lambda args: f"{helper(args[0])}[{helper(args[1])}:{helper(args[1])} + {args[2]}]",
        "list_take": lambda args: f"{helper(args[0])}[:{helper(args[1])}]",
        "Div": lambda args: f"{helper(args[0])} / {helper(args[1])}"
        if mode == "Float"
        else f"{helper(args[0])} // {helper(args[1])}",
        "Mul": lambda args: f"{helper(args[0])} * {helper(args[1])}",
        "Sub": lambda args: f"{helper(args[0])} - {helper(args[1])}",
        "Add": lambda args: f"{helper(args[0])} + {helper(args[1])}",
        "Mod": lambda args: f"{helper(args[0])} % {helper(args[1])}",
        "And": lambda args: " and ".join(helper(a) for a in args),
        "Or": lambda args: " or ".join(helper(a) for a in args),
        "Not": lambda args: f"not {helper(args[0])}",
        "vec_map": {
            "integer_exp": lambda args: f"tf.exp({helper(args[0])})",
            "integer_sqrt": lambda args: f"tf.sqrt({helper(args[0])})",
        },
        "matrix_selection_two_args": lambda args: f"tf.where({helper(args[0])}, {helper(args[1])}, {helper(args[2])})",
    }
    vars_to_replace = {"int_x": "base", "int_y": "active"}

    def helper(expr):
        if isinstance(expr, Call):
            if expr.name() == "vec_map":
                map_fn_name = all_synthesized_fns["map_int_to_int"].body().name()
                return translations[expr.name()][map_fn_name]([expr.arguments()[0]])
            if expr.name() == "matrix_selection_two_args":
                select_two_args_body = all_synthesized_fns["select_two_args"].body()
                cond = select_two_args_body.c()
                if_then = select_two_args_body.e1()
                if_else = select_two_args_body.e2()
                return translations[expr.name()]((cond, if_then, if_else))
        elif isinstance(expr, Lit):
            return f"{expr.val()}"
        elif expr.__class__.__name__ in translations.keys():
            return translations[expr.__class__.__name__](expr.args)
        else:
            name = "%s" % (expr)
            return vars_to_replace.get(name, name)

    return helper(ps_expr)
