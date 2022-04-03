from dataclasses import dataclass
import ir
import typing
import itertools


class Lattice:
    def ir_type(self) -> ir.Type:
        raise NotImplementedError()

    def merge(self, a: ir.Expr, b: ir.Expr) -> ir.Expr:
        raise NotImplementedError()

    def bottom(self) -> ir.Expr:
        raise NotImplementedError()

    def check_is_valid(self, v: ir.Expr) -> ir.Expr:
        raise NotImplementedError()


@dataclass(frozen=True)
class MaxInt(Lattice):
    int_type: ir.Type = ir.Int()

    def ir_type(self) -> ir.Type:
        return self.int_type

    def merge(self, a: ir.Expr, b: ir.Expr) -> ir.Expr:
        a_var = ir.Var("max_merge_a", self.int_type)
        b_var = ir.Var("max_merge_b", self.int_type)
        return ir.Let(
            a_var, a, ir.Let(b_var, b, ir.Ite(ir.Ge(a_var, b_var), a_var, b_var))
        )

    def bottom(self) -> ir.Expr:
        # only really makes sense for clocks, for others is just a default
        return ir.Lit(0, self.int_type)

    def check_is_valid(self, v: ir.Expr) -> ir.Expr:
        if self.int_type == ir.ClockInt():
            return ir.Ge(v, self.bottom())
        else:
            return ir.BoolLit(True)


@dataclass(frozen=True)
class PosBool(Lattice):
    def ir_type(self) -> ir.Type:
        return ir.Bool()

    def merge(self, a: ir.Expr, b: ir.Expr) -> ir.Expr:
        return ir.Or(a, b)

    def bottom(self) -> ir.Expr:
        return ir.BoolLit(False)

    def check_is_valid(self, v: ir.Expr) -> ir.Expr:
        return ir.BoolLit(True)


@dataclass(frozen=True)
class NegBool(Lattice):
    def ir_type(self) -> ir.Type:
        return ir.Bool()

    def merge(self, a: ir.Expr, b: ir.Expr) -> ir.Expr:
        return ir.And(a, b)

    def bottom(self) -> ir.Expr:
        return ir.BoolLit(True)

    def check_is_valid(self, v: ir.Expr) -> ir.Expr:
        return ir.BoolLit(True)


@dataclass(frozen=True)
class Set(Lattice):
    innerType: ir.Type

    def ir_type(self) -> ir.Type:
        return ir.Set(self.innerType)

    def merge(self, a: ir.Expr, b: ir.Expr) -> ir.Expr:
        return ir.Call("set-union", ir.Set(self.innerType), a, b)

    def bottom(self) -> ir.Expr:
        return ir.Call("set-create", ir.Set(self.innerType))

    def check_is_valid(self, v: ir.Expr) -> ir.Expr:
        return ir.BoolLit(True)


@dataclass(frozen=True)
class Map(Lattice):
    keyType: ir.Type
    valueType: Lattice

    def ir_type(self) -> ir.Type:
        return ir.Map(self.keyType, self.valueType.ir_type())

    def merge(self, a: ir.Expr, b: ir.Expr) -> ir.Expr:
        v_a = ir.Var("map_merge_a", self.valueType.ir_type())
        v_b = ir.Var("map_merge_b", self.valueType.ir_type())

        return ir.Call(
            "map-union",
            ir.Map(self.keyType, self.valueType.ir_type()),
            a,
            b,
            ir.Lambda(
                self.valueType.ir_type(), self.valueType.merge(v_a, v_b), v_a, v_b
            ),
        )

    def bottom(self) -> ir.Expr:
        return ir.Call("map-create", self.ir_type())

    def check_is_valid(self, v: ir.Expr) -> ir.Expr:
        merge_a = ir.Var("merge_into", ir.Bool())
        merge_b = ir.Var("merge_v", self.valueType.ir_type())

        return ir.Call(
            "map-fold-values",
            ir.Bool(),
            v,
            ir.Lambda(
                ir.Bool(),
                ir.And(merge_a, self.valueType.check_is_valid(merge_b)),
                merge_b,
                merge_a,
            ),
            ir.BoolLit(True),
        )


@dataclass(frozen=True)
class CascadingTuple(Lattice):
    l1: Lattice
    l2: Lattice

    def ir_type(self) -> ir.Type:
        return ir.Tuple(self.l1.ir_type(), self.l2.ir_type())

    def merge(self, a: ir.Expr, b: ir.Expr) -> ir.Expr:
        mergeA = ir.Var("cascade_merge_a", a.type)
        mergeB = ir.Var("cascade_merge_b", b.type)

        keyA = ir.TupleGet(mergeA, ir.IntLit(0))
        keyB = ir.TupleGet(mergeB, ir.IntLit(0))
        valueA = ir.TupleGet(mergeA, ir.IntLit(1))
        valueB = ir.TupleGet(mergeB, ir.IntLit(1))

        keyMerged = self.l1.merge(keyA, keyB)
        valueMerged = self.l2.merge(valueA, valueB)

        return ir.Let(
            mergeA,
            a,
            ir.Let(
                mergeB,
                b,
                ir.MakeTuple(
                    keyMerged,
                    ir.Ite(
                        ir.Or(
                            ir.Eq(keyA, keyB),
                            ir.And(
                                ir.Not(ir.Eq(keyA, keyMerged)),
                                ir.Not(ir.Eq(keyB, keyMerged)),
                            ),
                        ),
                        valueMerged,
                        ir.Ite(ir.Eq(keyA, keyMerged), valueA, valueB),
                    ),
                ),
            ),
        )

    def bottom(self) -> ir.Expr:
        return ir.MakeTuple(self.l1.bottom(), self.l2.bottom())

    def check_is_valid(self, v: ir.Expr) -> ir.Expr:
        return ir.And(
            self.l1.check_is_valid(ir.TupleGet(v, ir.IntLit(0))),
            self.l2.check_is_valid(ir.TupleGet(v, ir.IntLit(1))),
        )


def gen_types(depth: int) -> typing.Iterator[ir.Type]:
    if depth == 1:
        yield ir.Int()
        yield ir.ClockInt()
        yield ir.BoolInt()
        yield ir.OpaqueInt()
        yield ir.Bool()
    else:
        for innerType in gen_types(depth - 1):
            yield innerType
            # TODO: anything else?


int_like = {ir.Int().name, ir.ClockInt().name, ir.BoolInt().name, ir.OpaqueInt().name}
comparable_int = {ir.Int().name, ir.ClockInt().name}
set_supported_elem = {ir.Int().name, ir.OpaqueInt().name}


def gen_lattice_types(depth: int) -> typing.Iterator[Lattice]:
    if depth == 1:
        yield PosBool()
        yield NegBool()

    for innerType in gen_types(depth):
        if innerType.name in comparable_int:
            yield MaxInt(innerType)

    if depth > 1:
        for innerLatticeType in gen_lattice_types(depth - 1):
            yield innerLatticeType

        for innerType in gen_types(depth - 1):
            if innerType.name in set_supported_elem:
                yield Set(innerType)

        for keyType in gen_types(depth - 1):
            if keyType.name in set_supported_elem:
                for valueType in gen_lattice_types(depth - 1):
                    yield Map(keyType, valueType)

        for innerTypePair in itertools.permutations(gen_lattice_types(depth - 1), 2):
            yield CascadingTuple(*innerTypePair)


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
                if tuple(lattice_types) in seen:
                    continue
                else:
                    seen.add(tuple(lattice_types))
                    yield lattice_types
            cur_tuple_size += 1
        cur_type_depth += 1
