import os
import sys

from metalift.analysis import CodeInfo, analyze
from metalift.ir import (
    Choose,
    And,
    Ge,
    Eq,
    Le,
    Sub,
    Synth,
    Call,
    Int,
    IntLit,
    FnDeclRecursive,
    Var,
    Add,
    Ite,
    Gt,
)


# # programmatically generated grammar
# from synthesis import toSMT


def grammar(ci: CodeInfo):
    name = ci.name

    # ps
    return Ite(Gt(ci.readVars[0], IntLit(10)), IntLit(1), IntLit(0))


# sum_n (x : int):
#   if x >= 1: return x + sum_n(x - 1)
#   else: return 0
def targetLang():
    return []


if __name__ == "__main__":
    filename = "tests/ite3.ll"
    basename = "ite3"

    fnName = "test"
    loopsFile = "tests/ite3.loops"
    cvcPath = "cvc5"

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

    print("vars: %s" % invAndPs)
    # print("final: %s" % toSMT(targetLang(), invAndPs, vars, preds, vc, "tests/ite3.smt", False))

    # print("====== synthesis")
    # invAndPs = [grammar(ci) for ci in loopAndPsInfo]
    #
    # lang = targetLang()
    #
    # candidates = synthesize_new(lang, invAndPs, vars, preds, vc, cvcPath, basename)
