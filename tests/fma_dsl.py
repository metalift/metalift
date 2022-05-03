import os
import sys

from metalift.analysis import CodeInfo, analyze
from ir import *

from synthesize_auto import synthesize

# # programmatically generated grammar

# (synth-fun ps ( (tmp14 Int) (arg Int) ) Bool
#  ((B Bool) (C Bool) (D Bool) (E Int) (F Int))
#  ((B Bool ((or C D)))
#  (C Bool ((>= F arg)))
#  (D Bool ((= E (sum_n (- arg F)))))
#  (E Int (tmp14))
#  (F Int (1))))

# (synth-fun inv0 ((tmp1 Int) (tmp2 Int) (arg Int) ) Bool
#    ((B Bool) (C Bool) (D Bool) (E Int) (F Int))
#    ((B Bool ((or C D)))
#    (C Bool ((>= 1 arg) ))
#    (D Bool ((and (>= E 1) (<= E arg) (= E (sum_n (- E F))))))
#    (E Int (tmp1 tmp2))
#    (F Int (1))))


def grammar(ci: CodeInfo):
    # print("Looking at", ci)
    # print("read", ci.readVars)
    # print("mod", ci.modifiedVars)
    name = ci.name

    if name.startswith("inv"):
        raise RuntimeError("no invariants for loop-less grammar")
    else:  # ps
        inputVars = Choose(*ci.readVars, IntLit(0))
        rv = ci.modifiedVars[0]
        var_or_add = Add(inputVars, inputVars)
        var_or_fma = Choose(
            *ci.readVars, Call("fma", Int(), var_or_add, var_or_add, var_or_add)
        )
        summary = Eq(rv, Add(var_or_fma, var_or_fma))
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def targetLang():
    x = Var("x", Int())
    y = Var("y", Int())
    z = Var("z", Int())
    sum_n = FnDecl(
        "sum_n",
        Int(),
        Ite(
            Ge(x, IntLit(1)), Add(x, Call("sum_n", Int(), Sub(x, IntLit(1)))), IntLit(0)
        ),
        x,
    )
    fma = FnDeclNonRecursive("fma", Int(), Add(x, Mul(y, z)), x, y, z)
    return [sum_n, fma]


if __name__ == "__main__":
    filename = "tests/fma_dsl.ll"
    basename = "fma_dsl"

    fnName = "test"
    loopsFile = "tests/fma_dsl.loops"
    cvcPath = "cvc5"

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

    print("====== grammar")
    invAndPs = [grammar(ci) for ci in loopAndPsInfo]

    lang = targetLang()

    # rosette synthesizer  + CVC verfication
    print("====== synthesis")
    candidates = synthesize(
        basename, lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath
    )
    print("====== verified candidates")
    print("\n\n".join(str(c) for c in candidates))
