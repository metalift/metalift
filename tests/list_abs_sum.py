from typing import cast

from metalift.analysis import CodeInfo, analyze
from metalift.ir import *

from metalift.synthesize_auto import synthesize

# We use test_abs instead of abs because abs is reserved in cvc5.
TEST_ABS_FN_NAME = "test_abs"
LIST_ABS_SUM_FN_NAME = "list_abs_sum"

def grammar(ci: CodeInfo):
    name = ci.name
    read_var = ci.readVars[0]
    modified_var = Choose(*ci.modifiedVars)
    if name.startswith("inv"):
        int_lit = Choose(Sub(IntLit(0), IntLit(1)), IntLit(0), IntLit(1), IntLit(2))
        lst_length = Call(
            "list_length",
            Int(),
            read_var
        )
        lst_sum = Call(
            LIST_ABS_SUM_FN_NAME, 
            Int(), 
            read_var
        )
        lst_tail_sum = Call(
            LIST_ABS_SUM_FN_NAME, 
            Int(), 
            Call(
                "list_tail", 
                Int(), 
                read_var,
                Add(modified_var, int_lit)
            ) 
        )
        index_lower_bound = Choose(
            Ge(modified_var, int_lit),
            Gt(modified_var, int_lit),
        )
        index_upper_bound = Choose(
            Le(modified_var, lst_length),
            Lt(modified_var, lst_length),
        )
        body = And(
            And(index_lower_bound, index_upper_bound),
            Choose(
                Eq(Add(modified_var, lst_tail_sum), lst_sum),
                Eq(modified_var, lst_tail_sum)
            )
        )
        return Synth(ci.name, body, *ci.modifiedVars, *ci.readVars)

    else:  # ps
        lst_sum = Call(
            LIST_ABS_SUM_FN_NAME, 
            Int(), 
            read_var
        )
        return Synth(name, Eq(modified_var, lst_sum), *ci.modifiedVars, *ci.readVars)

def target_lang():
    lst = Var("lst", ListT(Int()))
    list_abs_sum = FnDeclRecursive(
        LIST_ABS_SUM_FN_NAME, 
        Int(),
        Ite(
            Ge(Call("list_length", Int(), lst), IntLit(1)), 
            Add(
                Ite(
                    Lt(Call("list_get", Int(), lst, IntLit(0)), IntLit(0)), 
                    Sub(IntLit(0), Call("list_get", Int(), lst, IntLit(0))), 
                    Call("list_get", Int(), lst, IntLit(0))
                ),
                Call(
                    LIST_ABS_SUM_FN_NAME,
                    Int(),
                    Call("list_tail", ListT(Int()), lst, IntLit(1)),
                )
            ), 
            IntLit(0)
        ),
        lst
    )
    return [list_abs_sum]

def eval(expr):            
    if isinstance(expr, Var):
        return expr.name()
    if isinstance(expr, Lit):
        return "%s"%(expr.val())
    if isinstance(expr, ValueRef):
        return expr.name
    if isinstance(expr, And):
        return " and ".join([eval(arg) for arg in expr.args])
    if isinstance(expr, Gt):
        return f"{eval(expr.e1())} > {eval(expr.e2())}"
    if isinstance(expr, Le):
        return f"{eval(expr.e1())} <= {eval(expr.e2())}"
    if isinstance(expr, Eq):
        return "%s = %s"%(eval(expr.e1()), eval(expr.e2()))
    if isinstance(expr, Sub):
        return f"{eval(expr.args[0])} - {eval(expr.args[1])}"
    if isinstance(expr, Add):
        return "%s + %s"%(eval(expr.args[0]), eval(expr.args[1]))
    if isinstance(expr, Call):
        eval_args = []
        for a in expr.arguments():
            eval_args.append(eval(a))
        return "%s(%s)"%(expr.name(), ', '.join(eval_args))
    else:
        return "%s"%(expr)
        
def code_gen(summary: FnDeclRecursive):
    return f'def {summary.name()}({", ".join([str(eval(a)) for a in summary.arguments()])}):\n  ' \
                                f'return {eval(summary.body())}'

def process_candidate_func(fn_def) -> FnDeclRecursive:
    retVal = cast(Eq, fn_def.body()).e1()
    args = filter(lambda v: v != retVal, fn_def.arguments())
    args = [
        Var(a.name, a.type) if isinstance(a, ValueRef) else a
        for a in args
    ]
    return FnDeclRecursive(
        fn_def.name(), 
        fn_def.returnT(), 
        cast(Eq, fn_def.body()).e2(), 
        *args
    )

if __name__ == "__main__":
    basename = "list_abs_sum"
    filename = f"tests/{basename}.ll"
    loops_filename = f"tests/{basename}.loops"
    fn_name = "forward_sum"
    cvc_path = "cvc5"

    (vars, inv_and_ps, preds, vc, loop_and_ps_info) = analyze(filename, fn_name, loops_filename)

    print("====== synthesis")
    inv_and_ps = [grammar(ci) for ci in loop_and_ps_info]

    lang = target_lang()

    # rosette synthesizer + CVC verfication
    candidates = synthesize(
        basename, lang, vars, inv_and_ps, preds, vc, loop_and_ps_info, cvc_path
    )
    print("====== verified candidates")
    for c in candidates:
        print(c, "\n")

    print("====== summary in target language")

    fn_def = process_candidate_func(candidates[1])
    print(code_gen(fn_def))