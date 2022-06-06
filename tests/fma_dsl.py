import os
import sys

from metalift.analysis import CodeInfo, analyze
from metalift.ir import *

from metalift.synthesize_auto import synthesize

def grammar(ci: CodeInfo):
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
    fma = FnDeclNonRecursive("fma", Int(), Add(x, Mul(y, z)), x, y, z)
    return [fma]


def codeGen(summary: FnDecl):
    expr = summary.body() 
    def eval(expr):
        if isinstance(expr, Eq):
            return "%s = %s"%(expr.e1(), eval(expr.e2()))
        if isinstance(expr, Add):
            return "%s + %s"%(eval(expr.args[0]), eval(expr.args[1]))
        if isinstance(expr, Call):
            eval_args = []
            for a in expr.arguments():
                eval_args.append(eval(a))
            return "%s(%s)"%(expr.name(), ', '.join(a for a in eval_args))
        if isinstance(expr, Lit):
            return "%s"%(expr.val())
        else:
            return "%s"%(expr)
    return eval(expr)


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
        basename, lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath, noVerify=True
    )
    summary = codeGen(candidates[0])
    print("====== summary in target language")
    print(summary)
    
