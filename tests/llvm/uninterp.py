from metalift.analysis import CodeInfo, analyze
from metalift.ir import Add, Call, Eq, FnDeclRecursive, Int, Synth, Var
from metalift.synthesize_rosette import synthesize

# define an uninterpreted function in the target language that doesn't have a body
# it should have the same name as the uninterpreted fn that we don't want the VC generator
# to process in the source (otherwise why are you using an uninterpreted function?)
uninterpFnName = "uninterp"


def uninterp(x: Var, y: Var):
    return Call(uninterpFnName, Int(), x, y)


def targetLang():
    x = Var("x", Int())
    y = Var("y", Int())
    uninterp = FnDeclRecursive(uninterpFnName, Int(), None, x, y)
    return [uninterp]


# postcondition for uninterp.c
def summary(r, x, y):
    return Eq(r, Add(uninterp(x, x), uninterp(y, y)))


def grammar(ci: CodeInfo):
    name = ci.name
    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        r = ci.modifiedVars[0]
        (x, y) = ci.readVars
        return Synth(name, summary(r, x, y), *ci.modifiedVars, *ci.readVars)


if __name__ == "__main__":
    filename = "tests/llvm/uninterp.ll"
    basename = "uninterp"

    fnName = "test"
    loopsFile = "tests/llvm/uninterp.loops"
    cvcPath = "cvc5"

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(
        filename, fnName, loopsFile, None, uninterpFuncs=[uninterpFnName]
    )

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
        uninterp_fns=[uninterpFnName]
    )
    print("====== verified candidates")
    for c in candidates:
        print(c, "\n")