import os
import sys
from analysis import CodeInfo, analyze
from ir import *
from synthesize_rosette import synthesize

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
                        List(Int()),
                        Call(
                            "list_take", List(Int()), ci.readVars[0], ci.modifiedVars[1]
                        ),
                        Call("lm", Fn(Int())),
                    ),
                    Call("lr", Fn(Int())),
                ),
            ),
            Ge(
                ci.modifiedVars[0],
                Call(
                    "reduce",
                    Int(),
                    Call(
                        "map",
                        List(Int()),
                        Call(
                            "list_take", List(Int()), ci.readVars[0], ci.modifiedVars[1]
                        ),
                        Call("lm", Fn(Int())),
                    ),
                    Call("lr", Fn(Int())),
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
        m = Choose(Call("lm", Fn(Int())))
        r = Choose(Call("lr", Fn(Int())))

        choices = Choose(
            Eq(
                rv,
                Call(
                    "reduce",
                    Int(),
                    Call("map", List(Int()), ci.readVars[0], Call("lm", Fn(Int()))),
                    Call("lr", Fn(Int())),
                ),
            ),
            Gt(
                rv,
                Call(
                    "reduce",
                    Int(),
                    Call("map", List(Int()), ci.readVars[0], Call("lm", Fn(Int()))),
                    Call("lr", Fn(Int())),
                ),
            ),
        )
        return Synth(name, choices, *ci.modifiedVars, *ci.readVars)
    else:
        raise Exception(f"Unknown function {name}")


def grammarFns(fns):

    if fns.args[0] == "lm":
        choices = Choose(IntLit(0), IntLit(1), IntLit(2), IntLit(3))
        return Synth(fns.args[0], choices, *fns.args[2:])
    else:
        v = Choose(fns.args[2:][0], fns.args[2:][1])
        choices = Choose(Add(v, v), Sub(v, v), Mul(v, v))
        return Synth(fns.args[0], choices, *fns.args[1:])


def targetLang():
    def list_length(l):
        return Call("list_length", Int(), l)

    def list_empty():
        return Call("list_empty", List(Int()))

    def list_get(l, i):
        return Call("list_get", Int(), l, i)

    def list_tail(l, i):
        return Call("list_tail", List(Int()), l, i)

    data = Var("data", List(Int()))
    arg2 = Var("val", Int())
    arg3 = Var("val2", Int())

    lm_fn = Var("f", Fn(Int()))
    lr_fn = Var("f", Fn(Int()))

    mapper = FnDecl("lm", Fn(Int()), "", arg2)
    reducer = FnDecl("lr", Fn(Int()), "", arg2, arg3)
    map_fn = FnDecl(
        "map",
        List(Int()),
        Ite(
            Eq(list_length(data), IntLit(0)),
            list_empty(),
            Call(
                "list_prepend",
                List(Int()),
                Call(lm_fn.args[0], Fn(Int()), list_get(data, IntLit(0))),
                Call("map", List(Int()), list_tail(data, IntLit(1)), lm_fn),
            ),
        ),
        data,
        lm_fn,
    )
    reduce_fn = FnDecl(
        "reduce",
        Int(),
        Ite(
            Eq(list_length(data), IntLit(0)),
            IntLit(0),
            Call(
                lr_fn.args[0],
                Fn(Int()),
                list_get(data, IntLit(0)),
                Call("reduce", Int(), list_tail(data, IntLit(1)), lr_fn),
            ),
        ),
        data,
        lr_fn,
    )

    return [map_fn, reduce_fn, mapper, reducer]


if __name__ == "__main__":

    filename = sys.argv[1]
    basename = os.path.splitext(os.path.basename(filename))[0]

    fnName = sys.argv[2]
    loopsFile = sys.argv[3]
    cvcPath = sys.argv[4]

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

    print("====== synthesis")
    invAndPs = [grammar(ci) for ci in loopAndPsInfo]

    lang = targetLang()
    fnsGrammar = []
    for l in lang:
        if l.args[1] == "":
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
        noVerify=True,
    )
    print("====== verified candidates")
    for c in candidates:
        print(c, "\n")
