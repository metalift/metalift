import os
import sys
from typing import List

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
)
from synthesize_rosette import synthesize
from rosette_translator import toRosette


def grammar(ci: CodeInfo):
    # print("Looking at", ci)
    # print("read", ci.readVars)
    # print("mod", ci.modifiedVars)
    name = ci.name

    if name.startswith("inv"):
        raise RuntimeError("no invariants for loop-less grammar")
    else:  # ps
        domino = DominoLang()
        domino.vars = [Choose(*ci.readVars) for _ in range(7)]
        rv = ci.modifiedVars[0]
        options = Choose(*list(domino.generate().values()))
        summary = Eq(rv, options)
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


class DominoLang(object):
    def __init__(self) -> None:
        super().__init__()
        self.vars = None
        self._consts = [0, 10, 20]
        self._consts = [IntLit(v) for v in self._consts]

    def _generate_mux(self):
        return {
            "Opt": (lambda x: Choose(IntLit(0), x)),
            "Mux2": (lambda x, y: Choose(x, y)),
            "Mux3": (lambda x, y, z: Choose(x, y, z)),
        }

    def _generate_arith_ops(self):
        return {"arith_op": (lambda x, y: Choose(Add(x, y), Sub(x, y)))}

    def _generate_const(self):
        return {"C": Choose(*self.vars, *self._consts)}

    def _generate_rel_op(self):
        return {
            "rel_op": (lambda x, y: Choose(Eq(x, y), Le(x, y), Ge(x, y), Not(Eq(x, y))))
        }

    def generate_templates(self):
        lib = {
            **self._generate_const(),
            **self._generate_arith_ops(),
            **self._generate_rel_op(),
            **self._generate_mux(),
        }

        state_1, state_2, pkt_1, pkt_2, pkt_3, pkt_4, pkt_5 = self.vars[:7]
        Mux2, Mux3 = lib["Mux2"], lib["Mux3"]
        Opt = lib["Opt"]
        C = lib["C"]

        # atom_template(int state_1, int state_2, int pkt_1, int pkt_2, int pkt_3, int pkt_4, int pkt_5)
        hash_fn = Add
        return {
            "if_else_raw": hash_fn(
                Ite(
                    lib["rel_op"](Opt(state_1), Mux3(pkt_1, pkt_2, C)),
                    Add(Opt(state_1), Mux3(pkt_1, pkt_2, C)),
                    Add(Opt(state_1), Mux3(pkt_1, pkt_2, C)),
                ),
                *self.vars[1:7]
            ),
            "mul_acc": hash_fn(
                Add(
                    Mul(Opt(state_1), Mux2(pkt_1, C)),
                    Mux2(pkt_2, pkt_3),
                    Mux2(pkt_2, pkt_3),
                ),
                *self.vars[1:7]
            ),
            # FnDecl("nested_ifs", Int(), hash_fn(None, *self.vars[1:7]), self.vars[:7]), # TODO
            # FnDecl("pair", Int(), hash_fn(None, *self.vars[1:7]), self.vars[:7]), # TODO
            "pred_raw": hash_fn(
                Ite(
                    lib["rel_op"](Opt(state_1), Mux3(pkt_1, pkt_2, C)),
                    Add(Opt(state_1), Mux3(pkt_1, pkt_2, C)),
                    state_1,
                ),
                *self.vars[1:7]
            ),
            "raw": hash_fn(Add(Opt(state_1), Mux2(pkt_1, C)), *self.vars[1:7]),
            "rw": hash_fn(Mux2(pkt_1, C), *self.vars[1:7]),
            "sub": hash_fn(
                Ite(
                    lib["rel_op"](Opt(state_1), Mux3(pkt_1, pkt_2, C)),
                    Add(Opt(state_1), lib["arith_op"](Mux3(pkt_1, pkt_2, C), Mux3(pkt_1, pkt_2, C))),
                    Add(Opt(state_1), lib["arith_op"](Mux3(pkt_1, pkt_2, C), Mux3(pkt_1, pkt_2, C))),
                ),
                *self.vars[1:7]
            ),
        }

    def generate(self):
        return self.generate_templates()


def targetLang():
    return [
        FnDecl("name", Int(), Choose(IntLit(0), IntLit(1)))
    ]


if __name__ == "__main__":
    filename = sys.argv[1]
    basename = os.path.splitext(os.path.basename(filename))[0]

    fnName = sys.argv[2]
    loopsFile = sys.argv[3]
    cvcPath = sys.argv[4]

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

    print("====== lang")
    lang = targetLang()

    print("====== grammar")
    invAndPs = [grammar(ci) for ci in loopAndPsInfo]


    # rosette synthesizer  + CVC verfication
    print("====== synthesis")
    candidates = synthesize(
        basename, lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath
    )
    print("====== verified candidates")
    print("\n\n".join(str(c) for c in candidates))
