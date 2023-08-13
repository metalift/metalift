from metalift.analysis import analyze
from metalift.ir import *

from metalift.synthesize_auto import synthesize


def grammar(name, args, ret):
    intLit = Choose(IntLit(1), IntLit(2), IntLit(3), IntLit(10))
    cond = Choose(
        Eq(*args, intLit), Gt(*args, intLit), Le(*args, intLit)
    )
    ite = Ite(cond, intLit, intLit)
    summary = Eq(ret, ite)
    return Synth(name, summary, ret, *args)


def targetLang():
    return []


if __name__ == "__main__":
    filename = "tests/llvm/ite1.ll"
    basename = "ite1"

    fnName = "test"
    loopsFile = "tests/llvm/ite1.loops"
    cvcPath = "cvc5"

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

    print("====== synthesis")
    invAndPs = [grammar(ci) for ci in loopAndPsInfo]

    lang = targetLang()

    candidates = synthesize(
        basename,
        lang,
        vars,
        invAndPs,
        preds,
        vc,
        loopAndPsInfo,
        cvcPath,
    )
    print("====== verified candidates")
    for c in candidates:
        print(c, "\n")

