from typing import List
from metalift.analysis_new import VariableTracker, analyze
from metalift.ir import *

from metalift.synthesize_auto import synthesize

# We use test_abs instead of abs because abs is reserved in cvc5.
TEST_ABS_FN_NAME = "test_abs"

def grammar(name, args, ret):
    def vars(depth: int, *read_args: Var) -> Choose:
        if depth == 0:
            return Choose(*read_args)
        else:
            depth_0 = vars(0, *read_args)
            last_depth = vars(depth - 1, *read_args)
            return Choose(depth_0, Add(depth_0, last_depth))
    
    var_or_add = vars(3, *args)
    abs_var_or_add = Call(TEST_ABS_FN_NAME, Int(), var_or_add)
    overall_add = vars(3, Choose(var_or_add, abs_var_or_add))
    summary = Eq(ret, overall_add)
    return Synth(name, summary, ret, *args)


def target_lang():
    x = Var("x", Int())
    body = Ite(Lt(x, IntLit(0)), Sub(IntLit(0), x), x)
    test_abs = FnDecl(TEST_ABS_FN_NAME, Int(), body, x)
    return [test_abs]


def code_gen(summary: FnDeclRecursive):
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
    basename = "abs_dsl"
    filename = f"tests/{basename}.ll"
    loops_filename = f"tests/{basename}.loops"
    fn_name = "test"
    cvc_path = "cvc5"

    test_analysis = analyze(filename, fn_name, loops_filename)

    # Define variables to be used
    variable_tracker = VariableTracker()
    a = variable_tracker.variable("a", Int())
    b = variable_tracker.variable("b", Int())

    # Generate verification condition
    ret_vc = lambda ret: Call(fn_name, Bool(), ret, a, b)
    vc = test_analysis.call(a, b)(variable_tracker, ret_vc)

    # rosette synthesizer  + CVC verfication
    print("====== synthesis")
    synth_fun = grammar(fn_name, [a, b], Var("ret", Int()))
    candidates = synthesize(
        basename, target_lang(), variable_tracker.all(), [synth_fun], [], vc, [synth_fun], cvc_path
    )
    summary = code_gen(candidates[0])

    print("====== summary in target language")
    print(summary)
