from metalift.ir import Add, Call, Eq, Expr, Lit


def codegen(expr: Expr) -> str:
    def eval(expr: Expr) -> str:
        if isinstance(expr, Eq):
            return "%s = %s"%(expr.e1(), eval(expr.e2()))
        if isinstance(expr, Add):
            return "%s + %s"%(eval(expr.args[0]), eval(expr.args[1]))
        if isinstance(expr, Call):
            eval_args = []
            for a in expr.arguments():
                eval_args.append(eval(a))
            return "%s(%s)"%(expr.name(), ', '.join(a for a in eval_args))
        if isinstance(expr, Lit):
            return "%s"%(expr.val())
        else:
            return "%s"%(expr)
    return eval(expr)