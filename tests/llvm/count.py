import os
import sys
from metalift.analysis import CodeInfo, analyze
from metalift.ir import *
from metalift.synthesize_rosette import synthesize

# # programmatically generated grammar
def grammar(ci: CodeInfo):
    name = ci.name
    if name.startswith("inv"):

        i = Choose(IntLit(0), IntLit(1))
        e = Choose(
            Eq(
                ci.modifiedVars[0],
                Call(
                    "reduce",
                    Int(),
                    Call(
                        "map",
                        ListT(Int()),
                        Call(
                            "list_take", ListT(Int()), ci.readVars[0], ci.modifiedVars[1]
                        ),
                        Var("lm", FnT(Int(), Int())),
                    ),
                    Var("lr", FnT(Int(), Int(), Int())),
                ),
            ),
            Ge(
                ci.modifiedVars[0],
                Call(
                    "reduce",
                    Int(),
                    Call(
                        "map",
                        ListT(Int()),
                        Call(
                            "list_take", ListT(Int()), ci.readVars[0], ci.modifiedVars[1]
                        ),
                        Var("lm", FnT(Int(), Int())),
                    ),
                    Var("lr", FnT(Int(), Int(), Int())),
                ),
            ),
        )
        # i<=length(data)
        d = Choose(
            Ge(ci.modifiedVars[1], Call("list_length", Int(), *ci.readVars)),
            Le(ci.modifiedVars[1], Call("list_length", Int(), *ci.readVars)),
            Gt(ci.modifiedVars[1], Call("list_length", Int(), *ci.readVars)),
            Lt(ci.modifiedVars[1], Call("list_length", Int(), *ci.readVars)),
            Eq(ci.modifiedVars[1], Call("list_length", Int(), *ci.readVars)),
        )
        # i>=0
        c = Choose(
            Ge(ci.modifiedVars[1], i),
            Le(ci.modifiedVars[1], i),
            Gt(ci.modifiedVars[1], i),
            Lt(ci.modifiedVars[1], i),
            Eq(ci.modifiedVars[1], i),
        )
        b = Choose(And(And(c, d), e))
        return Synth(ci.name, b, *ci.modifiedVars, *ci.readVars)

    elif name.startswith("test"):  # ps
        rv = ci.modifiedVars[0]
        m = Choose(Var("lm", FnT(Int(), Int())))
        r = Choose(Var("lr", FnT(Int(), Int(), Int())))

        choices = Choose(
            Eq(
                rv,
                Call(
                    "reduce",
                    Int(),
                    Call("map", ListT(Int()), ci.readVars[0], Var("lm", FnT(Int(), Int()))),
                    Var("lr", FnT(Int(), Int(), Int())),
                ),
            ),
            Gt(
                rv,
                Call(
                    "reduce",
                    Int(),
                    Call("map", ListT(Int()), ci.readVars[0], Var("lm", FnT(Int(), Int()))),
                    Var("lr", FnT(Int(), Int(), Int())),
                ),
            ),
        )
        return Synth(name, choices, *ci.modifiedVars, *ci.readVars)
    else:
        raise Exception(f"Unknown function {name}")


def grammarFns(fns):
    import pdb; pdb.set_trace()
    if fns.args[0] == "lm":
        choices = Choose(IntLit(0), IntLit(1), IntLit(2), IntLit(3))
        return Synth(fns.args[0], choices, *fns.args[2:])
    else:
        v = Choose(fns.args[2:][0], fns.args[2:][1])
        choices = Choose(Add(v, v), Sub(v, v), Mul(v, v))
        return Synth(fns.args[0], choices, *fns.args[2:])


def targetLang():
    def list_length(l):
        return Call("list_length", Int(), l)

    def list_empty():
        return Call("list_empty", ListT(Int()))

    def list_get(l, i):
        return Call("list_get", Int(), l, i)

    def list_tail(l, i):
        return Call("list_tail", ListT(Int()), l, i)

    data = Var("data", ListT(Int()))
    arg2 = Var("val", Int())
    arg3 = Var("val2", Int())

    lm_fn = Var("f", FnT(Int(), Int()))
    lr_fn = Var("f", FnT(Int(), Int(), Int()))

    mapper = FnDeclRecursive("lm", Int(), None, arg2)
    reducer = FnDeclRecursive("lr", Int(), None, arg2, arg3)
    map_fn = FnDeclRecursive(
        "map",
        ListT(Int()),
        Ite(
            Eq(list_length(data), IntLit(0)),
            list_empty(),
            Call(
                "list_prepend",
                ListT(Int()),
                CallValue(lm_fn, list_get(data, IntLit(0))),
                Call("map", ListT(Int()), list_tail(data, IntLit(1)), lm_fn),
            ),
        ),
        data,
        lm_fn,
    )

    reduce_fn = FnDeclRecursive(
        "reduce",
        Int(),
        Ite(
            Eq(list_length(data), IntLit(0)),
            IntLit(0),
            CallValue(
                lr_fn,
                list_get(data, IntLit(0)),
                Call("reduce", Int(), list_tail(data, IntLit(1)), lr_fn),
            ),
        ),
        data,
        lr_fn,
    )

    mr_axiom_data = Var("data", ListT(Int()))
    mr_axiom_index = Var("index", Int())
    map_reduce_axiom = Axiom(
        Implies(
            And(Ge(mr_axiom_index, IntLit(0)), Lt(mr_axiom_index, list_length(mr_axiom_data))),
            Eq(
                Call(
                    "reduce",
                    Int(),
                    Call(
                        "map",
                        ListT(Int()),
                        Call(
                            "list_take",
                            ListT(Int()),
                            mr_axiom_data,
                            Add(mr_axiom_index, IntLit(1))
                        ),
                        Var("lm", FnT(Int(), Int()))
                    ),
                    Var("lr", FnT(Int(), Int(), Int())),
                ),
                Call(
                    "lr",
                    Int(),
                    Call(
                        "reduce",
                        Int(),
                        Call(
                            "map",
                            ListT(Int()),
                            Call(
                                "list_take",
                                ListT(Int()),
                                mr_axiom_data,
                                mr_axiom_index
                            ),
                            Var("lm", FnT(Int(), Int()))
                        ),
                        Var("lr", FnT(Int(), Int(), Int())),
                    ),
                    Call(
                        "lm",
                        Int(),
                        Call(
                            "list_get",
                            Int(),
                            mr_axiom_data,
                            mr_axiom_index
                        )
                    ),
                ),
            ),
        ),
        mr_axiom_data,
        mr_axiom_index,
    )

    return [map_fn, reduce_fn, map_reduce_axiom, mapper, reducer]


if __name__ == "__main__":

    filename = "tests/llvm/Count.ll"
    basename = "Count"

    fnName = "test"
    loopsFile = "tests/llvm/Count.loops"
    cvcPath = "cvc5"

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

    print("====== synthesis")
    invAndPs = [grammar(ci) for ci in loopAndPsInfo]

    lang = targetLang()
    fnsGrammar = []
    for l in lang:
        if l.args[1] == None:
            fnsGrammar.append(grammarFns(l))

    candidates = synthesize(
        basename,
        lang,
        vars,
        invAndPs + fnsGrammar,
        preds,
        vc,
        loopAndPsInfo,
        cvcPath,
    )
    print("====== verified candidates")
    for c in candidates:
        print(c, "\n")
