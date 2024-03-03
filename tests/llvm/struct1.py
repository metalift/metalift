from metalift.analysis import CodeInfo, analyze
from metalift.ir import *
from metalift.synthesize_rosette import synthesize


# postcondition for struct1.c
def summary(r, x, y):
    return Eq(r, Call("my_add", Int(), x, y))


def grammar(ci: CodeInfo):
    name = ci.name
    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        r = ci.modified_vars[0]
        (x, y) = ci.read_vars
        return Synth(name, summary(r, x, y), *ci.modified_vars, *ci.read_vars)


def targetLang():
    x = Var("x", Int())
    y = Var("y", Int())
    my_add = FnDeclRecursive("my_add", Int(), Add(x, y), x, y)
    return [my_add]


if __name__ == "__main__":
    filename = "tests/llvm/struct1.ll"
    basename = "struct1"

    fnName = "test"
    loopsFile = "tests/llvm/struct1.loops"

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
