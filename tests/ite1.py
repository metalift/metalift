from metalift.analysis_new import VariableTracker, analyze
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
    filename = "tests/ite1.ll"
    basename = "ite1"

    fnName = "test"
    loopsFile = "tests/ite1.loops"
    cvcPath = "cvc5"

    test_analysis = analyze(filename, fnName, loopsFile)

    variable_tracker = VariableTracker()
    i = variable_tracker.variable("i", Int())

    synth_fun = grammar(fnName, [i], Var("ret", Int()))

    vc = test_analysis.call(i)(variable_tracker, lambda ret: Call(
        fnName,
        Bool(),
        ret,
        i
    ))

    vars = variable_tracker.all()

    print("====== synthesis")
    invAndPs = [synth_fun]
    loopAndPsInfo = [synth_fun]

    lang = targetLang()
    candidates = synthesize(
        basename, lang, vars, invAndPs, [], vc, loopAndPsInfo, cvcPath
    )
    for c in candidates:
        print(c, "\n")
