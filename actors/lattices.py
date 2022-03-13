import ir
import typing
import itertools

Lattice = typing.Tuple[ir.Type, typing.Callable[[ir.Expr, ir.Expr], ir.Expr], ir.Expr]

MaxInt: Lattice = (ir.Int(), lambda a, b: ir.Ite(ir.Ge(a, b), a, b), ir.IntLit(0))


def Set(innerType: ir.Type) -> Lattice:
    return (
        ir.Set(innerType),
        lambda a, b: ir.Call("set-union", ir.Set(innerType), a, b),
        ir.Call(f"set-create", ir.Set(innerType)),
    )


def gen_types(depth: int) -> typing.Iterator[ir.Type]:
    if depth == 1:
        yield ir.Int()
        yield ir.Bool()
    else:
        for innerType in gen_types(depth - 1):
            yield innerType
            # TODO: anything else?


set_supported_elem = {ir.Int().name}


def gen_lattice_types(depth: int) -> typing.Iterator[typing.Any]:
    if depth == 1:
        yield MaxInt
    else:
        for innerType in gen_lattice_types(depth - 1):
            yield innerType

        for innerType in gen_types(depth - 1):
            if innerType.name in set_supported_elem:
                yield Set(innerType)
            # TODO: maps


def gen_structures() -> typing.Iterator[typing.Any]:
    cur_type_depth = 2
    seen = set()
    while True:
        print(f"Maximum type depth: {cur_type_depth}")
        cur_tuple_size = 2
        while cur_tuple_size < cur_type_depth * 2:
            print(f"Maximum tuple size: {cur_tuple_size}")
            for lattice_types in itertools.combinations_with_replacement(
                gen_lattice_types(cur_type_depth), cur_tuple_size
            ):
                lattice_just_ir_types = tuple([t[0] for t in lattice_types])
                if lattice_just_ir_types in seen:
                    continue
                else:
                    seen.add(lattice_just_ir_types)
                    yield lattice_types
            cur_tuple_size += 1
        cur_type_depth += 1
