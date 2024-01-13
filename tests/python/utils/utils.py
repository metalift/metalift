from metalift.ir import (
    Add,
    And,
    Call,
    Div,
    Eq,
    Expr,
    Ge,
    Gt,
    Ite,
    Le,
    Lit,
    Lt,
    Mul,
    Sub,
    TupleExpr,
)


def codegen(expr: Expr) -> str:
    def eval(expr: Expr) -> str:
        if isinstance(expr, Eq):
            return f"{expr.e1()} == {eval(expr.e2())}"
        if isinstance(expr, Add):
            return f"({eval(expr.args[0])} + {eval(expr.args[1])})"
        if isinstance(expr, Sub):
            return f"({eval(expr.args[0])} - {eval(expr.args[1])})"
        if isinstance(expr, Mul):
            return f"({eval(expr.args[0])} * {eval(expr.args[1])})"
        if isinstance(expr, Div):
            return f"({eval(expr.args[0])} / {eval(expr.args[1])})"
        if isinstance(expr, Call):
            eval_args = []
            for a in expr.arguments():
                eval_args.append(eval(a))
            return f"{expr.name()}({', '.join(a for a in eval_args)})"
        if isinstance(expr, Lit):
            return f"{expr.val()}"
        if isinstance(expr, TupleExpr):
            return f"({', '.join(eval(a) for a in expr.args)})"
        if isinstance(expr, Ite):
            return f"{eval(expr.e1())} if {eval(expr.c())} else {eval(expr.e2())}"
        if isinstance(expr, Lt):
            return f"{eval(expr.e1())} < {eval(expr.e2())}"
        if isinstance(expr, Le):
            return f"{eval(expr.e1())} <= {eval(expr.e2())}"
        if isinstance(expr, Gt):
            return f"{eval(expr.e1())} > {eval(expr.e2())}"
        if isinstance(expr, Ge):
            return f"{eval(expr.e1())} >= {eval(expr.e2())}"
        if isinstance(expr, And):
            return " and ".join(eval(a) for a in expr.args)
        else:
            return "%s" % (expr)

    return eval(expr)
