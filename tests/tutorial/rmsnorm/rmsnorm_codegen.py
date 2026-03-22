from metalift.ir import Call, Expr


def nki_codegen(expr: Expr) -> str:
    if isinstance(expr, Call):
        print("hi")
        import pdb

        pdb.set_trace()
