import os
import sys
from typing import Callable
from enum import IntEnum
import typing

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
import rosette_translator
from synthesize_rosette import synthesize


class DominoType(IntEnum):
    PRIMITIVE = 1
    LIST = 2


class DominoLang(object):
    def __init__(self, constants=[1, 10, 20]) -> None:
        super().__init__()
        self.vars = None
        self.set_constants(constants)

    def _generate_mux(self):
        return {
            "Opt": (lambda x: Choose(IntLit(0), x)),
            "Mux2": (lambda x, y: Choose(x, y)),
            # "Mux3": (lambda x, y, z: Choose(x, y, z)),
            "Mux3": (lambda x, y, z: Choose(x, z) if x == y else Choose(x, y, z)),
        }

    def _generate_arith_ops(self):
        return {"arith_op": (lambda x, y: Choose(Add(x, y), Sub(x, y), Mul(x, y)))}

    def set_constants(self, constants):
        self._consts = [IntLit(v) for v in constants]

    def _generate_const(self):
        return {"C": Choose(*self._consts)}

    def _generate_rel_op(self):
        return {
            "rel_op": (
                lambda x, y: Choose(
                    Eq(x, y),
                    Le(x, y),
                    Not(Le(x, y)),
                    Ge(x, y),
                    Not(Ge(x, y)),
                    Not(Eq(x, y)),
                )
            )
        }

    def reduce_with_op(self, arr, op):
        out = arr[0]
        for item in arr[1:]:
            out = op(item, out)
        return out

    def set_vars(self, vars):
        self.vars = vars

    def _get_vars(self):
        return [(var, DominoType.PRIMITIVE) for var in self.vars]

    @staticmethod
    def targetLang(uninterpFuncs: typing.List[typing.Tuple[str, int]] = []):
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

        lang = [get_empty_list, add_to_list, add_2_to_list, add_3_to_list]

        for name, nargs in uninterpFuncs:
            assert nargs <= 3, "Uninterpreted fn must have <= 3 arguments"
            assert nargs > 0, "Uninterpreted fn must have at least one argument"
            uninterpArgs = [arg, arg2, arg3][:nargs]
            uninterp = FnDecl(name, Int(), None, *uninterpArgs)
            lang.append(uninterp)

        return lang

    def generate_templates(
        self,
        vars,
        uninterpFuncs: typing.List[typing.Tuple[str, int]] = [],
    ):
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

        state_1 = state_2 = primitive_var
        pkt_1 = pkt_2 = pkt_3 = pkt_4 = pkt_5 = primitive_var

        # atom_template(int state_1, int state_2, int pkt_1, int pkt_2, int pkt_3, int pkt_4, int pkt_5)

        nested_if_pred = lambda: lib["rel_op"](
            Sub(
                Add(
                    Opt(state_1),
                    Mux3(pkt_1, pkt_2, IntLit(0)),
                ),
                Mux3(pkt_1, pkt_2, IntLit(0)),
            ),
            C,
        )  # rel_op(Opt(state_1) + Mux3(pkt_1, pkt_2, 0) - Mux3(pkt_1, pkt_2, 0), C())
        nested_if_val = lambda: Add(
            Opt(state_1), lib["arith_op"](Mux3(pkt_1, pkt_2, C), Mux3(pkt_1, pkt_2, C))
        )  # Opt(state_1) + arith_op(Mux3(pkt_1, pkt_2, C()),  Mux3(pkt_1, pkt_2, C()));

        pkt_or_const = Mux3(pkt_1, pkt_2, C)

        atoms = {
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
                Ite(
                    lib["rel_op"](Opt(state_1), pkt_or_const),
                    Add(Opt(state_1), pkt_or_const),
                    Add(Opt(state_1), pkt_or_const),
                ),
                DominoType.PRIMITIVE,
            ),
            "mul_acc": (
                Add(
                    Mul(Opt(state_1), Mux2(pkt_1, C)),
                    Mux2(pkt_2, pkt_3),
                    Mux2(pkt_2, pkt_3),
                ),
                DominoType.PRIMITIVE,
            ),
            "nested_ifs": (
                Ite(
                    nested_if_pred(),
                    Ite(nested_if_pred(), nested_if_val(), nested_if_val()),
                    Ite(nested_if_pred(), nested_if_val(), nested_if_val()),
                ),
                DominoType.PRIMITIVE,
            ),
            # FnDecl("pair", Int(), (None, *self.vars[1:7]), self.vars[:7]), # TODO
            "pred_raw": (
                Ite(
                    lib["rel_op"](Opt(state_1), pkt_or_const),
                    Add(Opt(state_1), pkt_or_const),
                    state_1,
                ),
                DominoType.PRIMITIVE,
            ),
            "raw": ((Add(Opt(state_1), Mux2(pkt_1, C))), DominoType.PRIMITIVE),
            "rw": ((Mux2(pkt_1, C)), DominoType.PRIMITIVE),
            "sub": (
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

        for name, nargs in uninterpFuncs:
            uninterp = Call(name, Int(), *([primitive_var] * nargs))
            atoms[f"uninterp_call_{name}"] = (uninterp, DominoType.PRIMITIVE)

        return atoms

    def generate(
        self,
        depth=1,
        restrict_to_atoms=None,
        only_list_returns=True,
        uninterpFuncs: typing.List[typing.Tuple[str, int]] = [],
    ):
        restricted = (
            lambda atoms: {
                k: v
                for k, v in atoms.items()
                if k in restrict_to_atoms or k.startswith("uninterp_call")
            }
            if restrict_to_atoms is not None
            else atoms
        )
        vars = self._get_vars()
        assert depth > 0
        power_set = set(vars)
        for i in range(depth):
            vars = list(power_set)
            atoms = restricted(
                self.generate_templates(vars, uninterpFuncs=uninterpFuncs)
            )
            power_set.update(atoms.values())

        return {
            k: v[0]
            for k, v in atoms.items()
            if not only_list_returns or v[1] == DominoType.LIST
        }

    def loopless_grammar(
        self,
        depth=2,
        atoms=None,
        uninterpFuncs: typing.List[typing.Tuple[str, int]] = [],
    ):
        def grammar(ci: CodeInfo):
            name = ci.name

            if name.startswith("inv"):
                raise RuntimeError("no invariants for loop-less grammar")
            else:  # ps
                self.set_vars(ci.readVars)
                generated = self.generate(
                    depth=depth, restrict_to_atoms=atoms, uninterpFuncs=uninterpFuncs
                )
                options = Choose(*list(generated.values()))
                print(generated)

                rv = ci.modifiedVars[0]
                summary = Choose(
                    # Eq(rv, options),
                    Call("list_eq", Bool(), rv, options),
                )
                return Synth(name, summary, *ci.modifiedVars, *ci.readVars)

        return grammar

    @staticmethod
    def driver_function(
        grammar: Callable,
        fnName=sys.argv[2],
        listBound=3,
        uninterpFuncs: typing.List[typing.Tuple[str, int]] = [],
    ):
        filename = sys.argv[1]
        basename = os.path.splitext(os.path.basename(filename))[0]

        loopsFile = sys.argv[3]
        cvcPath = sys.argv[4]

        (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(
            filename,
            fnName,
            loopsFile,
            uninterpFuncs=[name for name, nargs in uninterpFuncs],
        )

        print("====== lang")
        lang = DominoLang.targetLang(uninterpFuncs=uninterpFuncs)
        print(lang)

        print("====== grammar")
        invAndPs = [grammar(ci) for ci in loopAndPsInfo]

        # rosette synthesizer  + CVC verfication
        print(f"====== synthesis (fn: {fnName})")
        candidates = synthesize(
            basename,
            lang,
            vars,
            invAndPs,
            preds,
            vc,
            loopAndPsInfo,
            cvcPath,
            unboundedInts=True,
            listBound=listBound,
        )
        print("====== verified candidates")
        print("\n\n".join(str(c) for c in candidates))

    def multiple_component_driver(self, components: typing.List):
        for item in components:
            component, grammar_kwargs = item[:2]
            if len(item) > 2:
                driver_kwargs = item[2]
            else:
                driver_kwargs = {}

            if "uninterpFuncs" in driver_kwargs:
                grammar_kwargs["uninterpFuncs"] = driver_kwargs["uninterpFuncs"]

            grammar = self.loopless_grammar(**grammar_kwargs)

            driver_kwargs["listBound"] = driver_kwargs.pop("listBound", 3)

            self.driver_function(grammar, fnName=component, **driver_kwargs)


if __name__ == "__main__":
    print(
        "[!] You need to use `domino.py` as a library rather than calling it directly."
    )
