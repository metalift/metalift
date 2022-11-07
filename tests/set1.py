from metalift.analysis_new import VariableTracker, analyze
from metalift.ir import (
    Bool,
    Choose,
    Eq,
    Synth,
    Call,
    Int,
    IntLit,
    Ite,
    SetT,
    Var,
)

from metalift.synthesize_auto import synthesize


def grammar(name, args, ret):
    inputS = args[0]
    inputAdd = args[1]
    inputValue = args[2]
    outputVar = ret

    emptySet = Call("set-create", SetT(Int()))

    intLit = Choose(IntLit(0), IntLit(1), IntLit(2), IntLit(3))
    intValue = Choose(inputValue, intLit)

    condition = Eq(inputAdd, intLit)

    setIn = Choose(inputS, emptySet, Call("set-singleton", SetT(Int()), intValue))

    setTransform = Choose(
        setIn,
        Call("set-union", SetT(Int()), setIn, setIn),
        Call("set-minus", SetT(Int()), setIn, setIn),
    )

    chosenTransform = Ite(condition, setTransform, setTransform)

    summary = Eq(outputVar, chosenTransform)
    return Synth(name, summary, ret, *args)


def targetLang():
    return []

if __name__ == "__main__":
    filename = "tests/set1.ll"
    basename = "set1"

    fnName = "test"
    loopsFile = "tests/set1.loops"
    cvcPath = "cvc5"

    test_analysis = analyze(filename, fnName, loopsFile)

    variable_tracker = VariableTracker()
    s = variable_tracker.variable("s", SetT(Int()))
    add = variable_tracker.variable("add", Int())
    value = variable_tracker.variable("value", Int())

    synth_fun = grammar(fnName, [s, add, value], Var("ret", SetT(Int())))

    vc = test_analysis.call(s, add, value)(variable_tracker, lambda ret: Call(
        fnName,
        Bool(),
        ret,
        s, add, value
    ))

    vars = variable_tracker.all()

    print("====== synthesis")
    invAndPs = [synth_fun]
    loopAndPsInfo = [synth_fun]

    lang = targetLang()
    candidates = synthesize(
        basename, lang, vars, invAndPs, [], vc, loopAndPsInfo, cvcPath
    )
