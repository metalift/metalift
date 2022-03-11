import ir
import typing

Lattice = typing.Tuple[ir.Type, typing.Callable[[ir.Expr, ir.Expr], ir.Expr], ir.Expr]

MaxInt: Lattice = (ir.Int(), lambda a, b: ir.Ite(ir.Ge(a, b), a, b), ir.IntLit(0))


def Set(innerType: ir.Type) -> Lattice:
    return (
        ir.Set(innerType),
        lambda a, b: ir.Call("set-union", ir.Set(innerType), a, b),
        ir.Call(f"set-create", ir.Set(innerType)),
    )
