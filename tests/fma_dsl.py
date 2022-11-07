from metalift.analysis_new import VariableTracker, analyze
from metalift.ir import *

from metalift.synthesize_auto import synthesize

def grammar(name, args, ret):
    inputVars = Choose(*args, IntLit(0))
    var_or_add = Add(inputVars, inputVars)
    var_or_fma = Choose(
        *args, Call("fma", Int(), var_or_add, var_or_add, var_or_add)
    )
    summary = Eq(ret, Add(var_or_fma, var_or_fma))
    return Synth(name, summary, ret, *args)


def targetLang():
    x = Var("x", Int())
    y = Var("y", Int())
    z = Var("z", Int())
    fma = FnDeclNonRecursive("fma", Int(), Add(x, Mul(y, z)), x, y, z)
    return [fma]


def codeGen(summary: FnDecl):
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
        else:
            return "%s"%(expr)
    return eval(expr)

if __name__ == "__main__":
    filename = "tests/fma_dsl.ll"
    basename = "fma_dsl"

    fnName = "test"
    loopsFile = "tests/fma_dsl.loops"
    cvcPath = "cvc5"

    test_analysis = analyze(filename, fnName, loopsFile)

    variable_tracker = VariableTracker()
    base = variable_tracker.variable("base", Int())
    arg1 = variable_tracker.variable("arg1", Int())
    base2 = variable_tracker.variable("base2", Int())
    arg2 = variable_tracker.variable("arg2", Int())

    synth_fun = grammar(fnName, [base, arg1, base2, arg2], Var("ret", Int()))

    vc = test_analysis.call(base, arg1, base2, arg2)(variable_tracker, lambda ret: Call(
        fnName,
        Bool(),
        ret,
        base, arg1, base2, arg2
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
