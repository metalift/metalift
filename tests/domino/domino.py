import os
import sys
from typing import List
from enum import IntEnum

from analysis import CodeInfo, analyze
from ir import (
    Choose,
    And,
    Expr,
    Ge,
    Eq,
    Le,
    Not,
    Sub,
    Synth,
    Call,
    Int,
    IntLit,
    Or,
    FnDecl,
    Var,
    Add,
    Mul,
    Ite,
    Tuple,
    List,
    Bool,
)
from synthesize_rosette import synthesize
from rosette_translator import toRosette


class DominoType(IntEnum):
    PRIMITIVE = 1
    LIST = 2


class DominoLang(object):
    def __init__(self, constants=[1, 10, 20]) -> None:
        super().__init__()
        self.vars = None
        self._consts = [IntLit(v) for v in constants]

    def _generate_mux(self):
        return {
            "Opt": (lambda x: Choose(IntLit(0), x)),
            "Mux2": (lambda x, y: Choose(x, y)),
            # "Mux3": (lambda x, y, z: Choose(x, y, z)),
            "Mux3": (lambda x, y, z: Choose(x, z) if x == y else Choose(x, y, z)),
        }

    def _generate_arith_ops(self):
        return {"arith_op": (lambda x, y: Choose(Add(x, y), Sub(x, y)))}

    def _generate_const(self):
        return {"C": Choose(*self.vars, *self._consts)}

    def _generate_rel_op(self):
        return {
            "rel_op": (lambda x, y: Choose(Eq(x, y), Le(x, y), Ge(x, y), Not(Eq(x, y))))
        }

    def reduce_with_op(self, arr, op):
        out = arr[0]
        for item in arr[1:]:
            out = op(item, out)
        return out

    def _get_vars(self):
        return [(var, DominoType.PRIMITIVE) for var in self.vars]

    @staticmethod
    def targetLang():
        arg = Var("n", Int())
        arg2 = Var("n2", Int())
        arg3 = Var("n3", Int())
        data = Var("l", List(Int()))
        get_empty_list = FnDecl(
            "GetEmptyList", List(Int()), Call("list_empty", List(Int()))
        )
        add_to_list = FnDecl(
            "AddStateRet",
            List(Int()),
            Call("list_append", List(Int()), Call("list_empty", List(Int())), arg),
            arg,
        )
        add_2_to_list = FnDecl(
            "AddStateRet2",
            List(Int()),
            Call(
                "list_append",
                List(Int()),
                Call("list_append", List(Int()), Call("list_empty", List(Int())), arg),
                arg2,
            ),
            arg,
            arg2,
        )
        add_3_to_list = FnDecl(
            "AddStateRet3",
            List(Int()),
            Call(
                "list_append",
                List(Int()),
                Call(
                    "list_append",
                    List(Int()),
                    Call(
                        "list_append", List(Int()), Call("list_empty", List(Int())), arg
                    ),
                    arg2,
                ),
                arg3,
            ),
            arg,
            arg2,
            arg3,
        )
        return [get_empty_list, add_to_list, add_2_to_list, add_3_to_list]

    def generate_templates(self, vars):
        lib = {
            **self._generate_const(),
            **self._generate_arith_ops(),
            **self._generate_rel_op(),
            **self._generate_mux(),
        }

        Mux2, Mux3 = lib["Mux2"], lib["Mux3"]
        Opt = lib["Opt"]
        C = lib["C"]
        empty_list = Call("GetEmptyList", List(Int()))

        primitive_var = Choose(
            *[var for (var, typ) in vars if typ == DominoType.PRIMITIVE]
        )
        list_var = [var for (var, typ) in vars if typ == DominoType.LIST] or [
            empty_list
        ]
        list_var = Choose(*list_var)

        base_vars = Choose(*[var for (var, _) in self._get_vars()])

        state_1 = state_2 = primitive_var
        pkt_1 = pkt_2 = pkt_3 = pkt_4 = pkt_5 = primitive_var

        # atom_template(int state_1, int state_2, int pkt_1, int pkt_2, int pkt_3, int pkt_4, int pkt_5)
        # hash_fn = lambda *arr: self.reduce_with_op(arr, Add)
        hash_fn = lambda x: x

        pkt_or_const = Mux3(pkt_1, pkt_2, C)
        # pkt_or_const = Choose(base_vars, C)
        # pkt_or_const = Choose(pkt_1, C)

        return {
            "stateless_arith": (
                lib["arith_op"](pkt_or_const, pkt_or_const),
                DominoType.PRIMITIVE,
            ),
            "stateless_rel": (
                lib["rel_op"](pkt_or_const, pkt_or_const),
                DominoType.PRIMITIVE,
            ),
            "const": (lib["C"], DominoType.PRIMITIVE),
            "if_else_raw": (
                hash_fn(
                    Ite(
                        lib["rel_op"](Opt(state_1), pkt_or_const),
                        Add(Opt(state_1), pkt_or_const),
                        Add(Opt(state_1), pkt_or_const),
                    ),
                ),
                DominoType.PRIMITIVE,
            ),
            "mul_acc": (
                hash_fn(
                    Add(
                        Mul(Opt(state_1), Mux2(pkt_1, C)),
                        Mux2(pkt_2, pkt_3),
                        Mux2(pkt_2, pkt_3),
                    ),
                ),
                DominoType.PRIMITIVE,
            ),
            # FnDecl("nested_ifs", Int(), hash_fn(None, *self.vars[1:7]), self.vars[:7]), # TODO
            # FnDecl("pair", Int(), hash_fn(None, *self.vars[1:7]), self.vars[:7]), # TODO
            "pred_raw": (
                hash_fn(
                    Ite(
                        lib["rel_op"](Opt(state_1), pkt_or_const),
                        Add(Opt(state_1), pkt_or_const),
                        state_1,
                    ),
                ),
                DominoType.PRIMITIVE,
            ),
            "raw": (hash_fn(Add(Opt(state_1), Mux2(pkt_1, C))), DominoType.PRIMITIVE),
            "rw": (hash_fn(Mux2(pkt_1, C)), DominoType.PRIMITIVE),
            "sub": (
                hash_fn(
                    Ite(
                        lib["rel_op"](Opt(state_1), pkt_or_const),
                        Add(
                            Opt(state_1),
                            lib["arith_op"](pkt_or_const, pkt_or_const),
                        ),
                        Add(
                            Opt(state_1),
                            lib["arith_op"](pkt_or_const, pkt_or_const),
                        ),
                    ),
                ),
                DominoType.PRIMITIVE,
            ),
            "add_state_var": (
                Call("AddStateRet", List(Int()), primitive_var),
                DominoType.LIST,
            ),
            "add_2_state_vars": (
                Call("AddStateRet2", List(Int()), primitive_var, primitive_var),
                DominoType.LIST,
            ),
            "add_3_state_vars": (
                Call(
                    "AddStateRet3",
                    List(Int()),
                    primitive_var,
                    primitive_var,
                    primitive_var,
                ),
                DominoType.LIST,
            ),
            "get_empty_list": (empty_list, DominoType.LIST),
        }

    def generate(self, depth=1, restrict_to_atoms=None, only_list_returns=True):
        restricted = (
            lambda atoms: {k: v for k, v in atoms.items() if k in restrict_to_atoms}
            if restrict_to_atoms is not None
            else atoms
        )
        vars = self._get_vars()
        assert depth > 0
        power_set = set(vars)
        for i in range(depth):
            vars = list(power_set)
            atoms = restricted(self.generate_templates(vars))
            power_set.update(atoms.values())

        return {
            k: v[0]
            for k, v in atoms.items()
            if not only_list_returns or v[1] == DominoType.LIST
        }


if __name__ == "__main__":
    print(
        "[!] You need to use `domino.py` as a library rather than calling it directly."
    )
