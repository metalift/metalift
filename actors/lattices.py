import ir
import typing

Lattice = typing.Tuple[ir.Type, typing.Callable[[ir.Expr, ir.Expr], ir.Expr], ir.Expr]

MaxInt: Lattice = (ir.Int(), lambda a, b: ir.Call("max", ir.Int(), a, b), ir.IntLit(0))


def Set(innerType: ir.Type) -> Lattice:
    return (
        ir.Set(innerType),
        lambda a, b: ir.Call("union", ir.Set(innerType), a, b),
        ir.Var(f"(as emptyset (Set {innerType}))", ir.Set(innerType)),
    )
