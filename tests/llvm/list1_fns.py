from metalift.analysis import CodeInfo, analyze
from metalift.ir import *
from metalift.synthesize_rosette import synthesize


# # programmatically generated grammar
def grammar(ci: CodeInfo):
    name = ci.name

    if name.startswith("inv"):
        f = Choose(
            Call("Select-pred", FnT(Bool(), *ci.readVars)),
            Call("Select-pred1", FnT(Bool(), *ci.readVars)),
            Call("Select-pred2", FnT(Bool(), *ci.readVars)),
        )
        a = Choose(
            ci.modifiedVars[0],
            *ci.readVars,
            Call("Select", ListT(Int()), *ci.readVars, f),
        )
        i = Choose(IntLit(0), IntLit(1))
        e = Choose(
            Call(
                "list_eq",
                Bool(),
                Call(
                    "list_concat",
                    ListT(Int()),
                    a,
                    Call(
                        "Select",
                        ListT(Int()),
                        Call("list_tail", ListT(Int()), a, ci.modifiedVars[1]),
                        f,
                    ),
                ),
                a,
            ),
            Call(
                "list_eq",
                Bool(),
                Call(
                    "list_concat",
                    ListT(Int()),
                    a,
                    Call("list_tail", ListT(Int()), a, ci.modifiedVars[1]),
                ),
                a,
            ),
        )
        d = Choose(
            Ge(ci.modifiedVars[1], Call("list_length", Int(), *ci.readVars)),
            Le(ci.modifiedVars[1], Call("list_length", Int(), *ci.readVars)),
            Gt(ci.modifiedVars[1], Call("list_length", Int(), *ci.readVars)),
            Lt(ci.modifiedVars[1], Call("list_length", Int(), *ci.readVars)),
            Eq(ci.modifiedVars[1], Call("list_length", Int(), *ci.readVars)),
        )
        c = Choose(
            Ge(ci.modifiedVars[1], i),
            Le(ci.modifiedVars[1], i),
            Gt(ci.modifiedVars[1], i),
            Lt(ci.modifiedVars[1], i),
            Eq(ci.modifiedVars[1], i),
        )
        b = Choose(And(And(c, d), e))
        return Synth(ci.name, b, *ci.modifiedVars, *ci.readVars)

    else:  # ps
        rv = ci.modifiedVars[0]
        fns = Choose(
            Call("Select-pred", FnT(Bool(), rv)),
            Call("Select-pred1", FnT(Bool(), rv)),
            Call("Select-pred2", FnT(Bool(), rv)),
        )
        choices = Choose(
            Call("list_eq", Bool(), rv, *ci.readVars),
            (
                Call(
                    "list_eq",
                    Bool(),
                    rv,
                    Call("Select", ListT(Int()), *ci.readVars, fns),
                )
            ),
        )

        return Synth(name, choices, *ci.modifiedVars, *ci.readVars)


def targetLang():
    arg = Var("n", Int())
    select_pred = FnDeclRecursive("Select-pred", FnT(Bool()), Gt(arg, IntLit(2)), arg)
    select_pred1 = FnDeclRecursive(
        "Select-pred1", FnT(Bool()), Lt(arg, IntLit(10)), arg
    )
    select_pred2 = FnDeclRecursive(
        "Select-pred2", FnT(Bool()), And(Gt(arg, IntLit(2)), Lt(arg, IntLit(10))), arg
    )
    data = Var("l", ListT(Int()))
    f = Var("f", FnT(Bool()))
    select_func = FnDeclRecursive(
        "Select",
        ListT(Int()),
        Ite(
            Eq(Call("list_length", Int(), data), IntLit(0)),
            Call("list_empty", ListT(Int())),
            Ite(
                CallValue(f, Call("list_get", Int(), data, IntLit(0))),
                Call(
                    "list_append",
                    ListT(Int()),
                    Call(
                        "Select",
                        ListT(Int()),
                        Call("list_tail", ListT(Int()), data, IntLit(1)),
                        f,
                    ),
                    Call("list_get", Int(), data, IntLit(0)),
                ),
                Call(
                    "Select",
                    ListT(Int()),
                    Call("list_tail", ListT(Int()), data, IntLit(1)),
                    f,
                ),
            ),
        ),
        data,
        f,
    )

    return [select_pred, select_pred1, select_pred2, select_func]


if __name__ == "__main__":
    filename = "tests/llvm/list1.ll"
    basename = "list1"

    fnName = "test"
    loopsFile = "tests/llvm/list1.loops"
    cvcPath = "cvc5"

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

    print("====== synthesis")
    invAndPs = [grammar(ci) for ci in loopAndPsInfo]

    lang = targetLang()
    # toRosette(basename+".rkt",lang,vars, invAndPs, preds, vc, loopAndPsInfo,[])

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
    # print("====== verified candidates")
    # for c in candidates:print(c,"\n")
