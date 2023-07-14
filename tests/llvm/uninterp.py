import typing

from metalift.analysis import CodeInfo, analyze
from metalift.ir import Eq, Synth, Call, Int, FnDeclRecursive, Var, Add
from metalift.rosette_translator import toRosette

from metalift.smt_util import toSMT

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
    cvcPath = ""

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(
        filename, fnName, loopsFile, None, uninterpFuncs=[uninterpFnName]
    )

    print("====== synthesis")
    invAndPs = [grammar(ci) for ci in loopAndPsInfo]

    lang = targetLang()
    invGuess: typing.List[typing.Any] = []
    unboundedInts = False
    synthDir = "./tests/llvm/"
    synthFile = synthDir + basename + ".rkt"

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
    exit(0)

    toRosette(
        synthFile,
        lang,
        vars,
        invAndPs,
        preds,
        vc,
        loopAndPsInfo,
        invGuess,
        unboundedInts,
        listBound=2
    )

    ### SMT
    print("====== verification")

    #####identifying call sites for inlining #####
    inCalls: typing.List[typing.Any] = []
    fnCalls: typing.List[typing.Any] = []

    ##### generating function definitions of all the functions to be synthesized#####
    candidatesSMT = []
    candidateDict = {}
    r = Var("tmp9", Int())
    x = Var("arg", Int())
    y = Var("arg1", Int())
    # pretend that we have run synthesis and insert the result into candidateDict to print
    candidateDict[fnName] = summary(r, x, y)

    for ce in loopAndPsInfo:
        allVars = (
            ce.modifiedVars + ce.readVars if isinstance(ce, CodeInfo) else ce.args[2:]
        )
        ceName = ce.name if isinstance(ce, CodeInfo) else ce.args[0]
        candidatesSMT.append(
            FnDeclRecursive(
                ceName,
                ce.retT if isinstance(ce, CodeInfo) else ce.type,
                candidateDict[ceName],
                *allVars,
            )
        )

    verifFile = synthDir + basename + ".smt"

    toSMT(lang, vars, candidatesSMT, preds, vc, verifFile, inCalls, fnCalls)
