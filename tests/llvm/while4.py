from metalift.analysis import CodeInfo, analyze
from metalift.ir import *
from metalift.synthesize_auto import synthesize


# # programmatically generated grammar
# (synth-fun inv0 ((tmp Int) (tmp1 Int) ) Bool
#    ((B Bool) (C Bool) (D Bool) (E Int) (F Int))
#    ((B Bool ((and C D)))
#    (C Bool ((= E (sum_n (- E F)))))
#    (D Bool ((and (>= E F) (<= E F))))
#    (E Int (tmp tmp1))
#    (F Int (1 2 3))))
# (synth-fun ps ( (tmp12 Int) ) Bool
#  ((B Bool) (C Int) (D Int))
#  ((B Bool ((= C (sum_n D))))
#  (C Int (tmp12))
#  (D Int (1 2))))
def grammar(ci: CodeInfo):
    name = ci.name

    if name.startswith("inv"):
        e = Choose(*ci.modified_vars)
        f = Choose(IntLit(1), IntLit(2), IntLit(3))
        c = Eq(e, Call("sum_n", Int(), Sub(e, f)))
        d = And(Ge(e, f), Le(e, f))
        b = And(c, d)
        return Synth(ci.name, b, *ci.modified_vars, *ci.read_vars)

    else:  # ps
        rv = ci.modified_vars[0]
        choices = Choose(IntLit(1), IntLit(2))
        b = Eq(rv, Call("sum_n", Int(), choices))
        return Synth(name, b, *ci.modified_vars, *ci.read_vars)


def targetLang():
    x = Var("x", Int())
    sum_n = FnDeclRecursive(
        "sum_n",
        Int(),
        Ite(
            Ge(x, IntLit(1)),
            Add(x, Call("sum_n", Int(), Sub(x, IntLit(1)))),
            IntLit(0),
        ),
        x,
    )
    return [sum_n]


if __name__ == "__main__":
    filename = "tests/llvm/while4.ll"
    basename = "while4"

    fnName = "test"
    loopsFile = "tests/llvm/while4.loops"
    cvcPath = "cvc5"

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

    print("====== synthesis")
    invAndPs = [grammar(ci) for ci in loopAndPsInfo]

    lang = targetLang()

    # rosette synthesizer  + CVC verfication
    candidates = synthesize(
        basename, lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath
    )
    print("====== verified candidates")
    for c in candidates:
        print(c, "\n")
