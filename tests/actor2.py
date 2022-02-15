from analysis import CodeInfo
from ir import *
from actor_util import synthesize_actor, check_aci
import actors.lattices as lat
from auto_grammar import auto_grammar
import sys
import os

if os.environ.get("SYNTH_CVC5") == "1":
    from synthesize_cvc5 import synthesize
else:
    from synthesize_rosette import synthesize

synthStateStructure = [lat.MaxInt, lat.MaxInt]
synthStateType = Tuple(*[a[0] for a in synthStateStructure])


def grammarEquivalence(inputState, synthState):
    return auto_grammar(Bool(), 2, inputState, synthState)


def grammarStateInvariant(synthState):
    return auto_grammar(Bool(), 1, synthState)


def grammarSupportedCommand(synthState, args):
    return auto_grammar(Bool(), 1, synthState, *args)


def inOrder(cmd1, cmd2):
    return BoolLit(True)


def grammarQuery(ci: CodeInfo):
    name = ci.name

    inputState = ci.readVars[0]
    outputVar = ci.modifiedVars[0]

    summary = Eq(outputVar, auto_grammar(parseTypeRef(outputVar.type), 2, inputState))

    return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def grammar(ci: CodeInfo):
    name = ci.name

    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        inputState = ci.readVars[0]
        stateVal1 = TupleGet(inputState, IntLit(0))
        stateVal2 = TupleGet(inputState, IntLit(1))

        inputAdd = ci.readVars[1]

        outputState = ci.modifiedVars[0]

        intLit = Choose(IntLit(0), IntLit(1))

        condition = Eq(inputAdd, intLit)

        intIn = Choose(stateVal1, stateVal2)

        intTransform = Choose(intIn, Add(intIn, intLit))

        intTransform = Choose(intTransform, Ite(condition, intTransform, intTransform))

        summary = Eq(
            outputState,
            MakeTuple(
                *[
                    synthStateStructure[i][1](
                        TupleGet(inputState, IntLit(i)), intTransform
                    )
                    for i in range(len(synthStateStructure))
                ]
            ),
        )

        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def initState():
    return MakeTuple(*[elem[2] for elem in synthStateStructure])


def targetLang():
    maxA = Var("a", Int())
    maxB = Var("b", Int())
    return [
        FnDeclNonRecursive("max", Int(), Ite(Ge(maxA, maxB), maxA, maxB), maxA, maxB),
    ]


if __name__ == "__main__":
    mode = sys.argv[1]
    filename = sys.argv[2]
    fnNameBase = sys.argv[3]
    loopsFile = sys.argv[4]
    cvcPath = sys.argv[5]

    if mode == "aci":
        check_aci(
            filename,
            fnNameBase,
            loopsFile,
            cvcPath,
        )
    else:
        synthesize_actor(
            filename,
            fnNameBase,
            loopsFile,
            cvcPath,
            synthStateType,
            initState,
            grammarStateInvariant,
            grammarSupportedCommand,
            inOrder,
            grammar,
            grammarQuery,
            grammarEquivalence,
            targetLang,
            synthesize,
            unboundedInts=True,
        )
