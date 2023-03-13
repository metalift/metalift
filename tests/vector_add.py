from metalift.analysis_new import VariableTracker, analyze
from metalift.ir import *

from metalift.synthesize_auto import synthesize

def grammar(name, args, ret):
    [a1, a2, a3, a4, b1, b2, b3, b4] = args
    a = Tuple(a1, a2, a3, a4)
    b = Tuple(b1, b2, b3, b4)

    add_pd = Call("add_pd", TupleT(Int(), Int(), Int(), Int()), Choose(a, b), Choose(a, b))

    # Add recursive depth of 5
    for _ in range(5):
        add_pd = Call("add_pd", TupleT(Int(), Int(), Int(), Int()), Choose(add_pd, a, b), Choose(add_pd, a, b))

    summary = Eq(ret, Call("reduce_add_pd", Int(), add_pd))
    return Synth(name, summary, ret, *args)

def targetLang():
    a = Var("a", TupleT(Int(), Int(), Int(), Int()))
    b = Var("b", TupleT(Int(), Int(), Int(), Int()))
    elem1 = Add(TupleGet(a, IntLit(0)), TupleGet(b, IntLit(0)))
    elem2 = Add(TupleGet(a, IntLit(1)), TupleGet(b, IntLit(1)))
    elem3 = Add(TupleGet(a, IntLit(2)), TupleGet(b, IntLit(2)))
    elem4 = Add(TupleGet(a, IntLit(3)), TupleGet(b, IntLit(3)))
    add_pd = FnDecl("add_pd", TupleT(Int(), Int(), Int(), Int()), Tuple(elem1, elem2, elem3, elem4), a, b)

    t = Var("t", TupleT(Int(), Int(), Int(), Int()))
    t_1 = TupleGet(t, IntLit(0))
    t_2 = TupleGet(t, IntLit(1))
    t_3 = TupleGet(t, IntLit(2))
    t_4 = TupleGet(t, IntLit(3))
    reduce_add_pd = FnDecl("reduce_add_pd", Int(), Add(t_1, t_2, t_3, t_4), t)

    return [add_pd, reduce_add_pd]


def codeGen(summary: FnDeclRecursive):
    expr = summary.body() 
    def eval(expr):
        if isinstance(expr, Eq):
            return "%s = %s"%(expr.e1(), eval(expr.e2()))
        if isinstance(expr, Add):
            return "%s + %s"%(eval(expr.args[0]), eval(expr.args[1]))
        if isinstance(expr, Call):
            eval_args = []
            for a in expr.arguments():
                eval_args.append(eval(a))
            return "%s(%s)"%(expr.name(), ', '.join(a for a in eval_args))
        if isinstance(expr, Lit):
            return "%s"%(expr.val())
        if isinstance(expr, Tuple):
            eval_args = []
            for a in expr.args:
                eval_args.append((eval(a)))
            return "(%s)"%(', '.join(a for a in eval_args))
        else:
            return "%s"%(expr)
    return eval(expr)

if __name__ == "__main__":
    filename = "tests/vector_add.ll"
    basename = "vector_add"

    fnName = "test"
    loopsFile = "tests/vector_add.loops"
    cvcPath = "cvc5"

    test_analysis = analyze(filename, fnName, loopsFile)

    variable_tracker = VariableTracker()
    a1 = variable_tracker.variable("a1", Int())
    a2 = variable_tracker.variable("a2", Int())
    a3 = variable_tracker.variable("a3", Int())
    a4 = variable_tracker.variable("a4", Int())
    b1 = variable_tracker.variable("b1", Int())
    b2 = variable_tracker.variable("b2", Int())
    b3 = variable_tracker.variable("b3", Int())
    b4 = variable_tracker.variable("b4", Int())

    synth_fun = grammar(fnName, [a1, a2, a3, a4, b1, b2, b3, b4], Var("ret", Int()))

    vc = test_analysis.call(a1, a2, a3, a4, b1, b2, b3, b4)(variable_tracker, lambda ret: Call(
        fnName,
        Bool(),
        ret,
        a1, a2, a3, a4, b1, b2, b3, b4
    ))

    vars = variable_tracker.all()
    loopAndPsInfo = [synth_fun]

    print("====== grammar")
    invAndPs = [synth_fun]

    lang = targetLang()

    # rosette synthesizer  + CVC verfication
    print("====== synthesis")
    candidates = synthesize(
        basename, lang, vars, invAndPs, [], vc, loopAndPsInfo, cvcPath
    )
    summary = codeGen(candidates[0])
    print("====== summary in target language")
    print(summary)