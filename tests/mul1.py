import shutil

from metalift.ir import *
from metalift.analysis import CodeInfo, analyze

from metalift.synthesize_auto import synthesize

MUL1D = "elementwise_mul"
SAME_LEN = "same_length"

def ml_list_get(lst, i):
    return Call("list_get", Int(), lst, i)

def ml_list_head(lst):
    return ml_list_get(lst, IntLit(0))

def ml_list_tail(lst):
    return Call("list_tail", ListT(Int()), lst)

def ml_list_prepend(e, lst):
    return Call("list_prepend", ListT(Int()), e, lst)

def ml_list_length(lst):
    return Call("list_length", Int(), lst)

def ml_list_empty():
    return Call("list_empty", ListT(Int()))

def ml_list_take(lst, i):
    return Call("list_take", ListT(Int()), lst, i)

def ml_min(a, b):
    return Ite(Lt(a, b), a, b)

def ml_mul1d(x, y):
    return Call(MUL1D, ListT(Int()), x, y)

def ml_same_len(x, y):
    return Call(SAME_LEN, Bool(), x, y)

def grammar(ci: CodeInfo):
    name = ci.name

    if name.startswith("inv"):
        # mV[0] is list, mV[1] is int
        #print(*ci.modifiedVars)
        print(*ci.readVars)
        #some_input = ci.readVars[0]
        #other_input = ci.readVars[1]
        an_input = Choose(*ci.readVars)

        prod = ci.modifiedVars[0]
        i = ci.modifiedVars[1]
        initial = Choose(Ge(i, IntLit(0)),
                         Gt(i, IntLit(0)),
                         Le(i, IntLit(0)),
                         Lt(i, IntLit(0)),
                         Eq(i, IntLit(0)),
                         Ge(i, IntLit(1)),
                         Gt(i, IntLit(1)),
                         Le(i, IntLit(1)),
                         Lt(i, IntLit(1)),
                         Eq(i, IntLit(1)))
        loop_cond = Choose(Lt(i, ml_list_length(an_input)),
                           Le(i, ml_list_length(an_input)),
                           Gt(i, ml_list_length(an_input)),
                           Ge(i, ml_list_length(an_input)),
                           Eq(i, ml_list_length(an_input)))
        post = Eq(prod, ml_mul1d(ml_list_take(an_input, i), ml_list_take(an_input, i)))
        inv = And(initial, loop_cond)
        summary = And(inv, post)
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)
    else:
        output = ci.modifiedVars[0]
        (x, y) = ci.readVars
        # change this to Implies
        #summary = Implies(ml_same_len(x, y), Eq(ml_mul1d(x, y), output))
        summary = Eq(ml_mul1d(x, y), output)
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)

def targetLang():
    # Assumes the lists are the same length
    def mul_body(x, y):
        size = ml_list_length(x)
        cur_prod = Mul(ml_list_head(x), ml_list_head(y))
        x_rest = ml_list_tail(x)
        y_rest = ml_list_tail(y)
        recursed = ml_mul1d(x_rest, y_rest)
        general_answer = ml_list_prepend(cur_prod, recursed)
        return Ite(Eq(size, IntLit(0)), ml_list_empty(), general_answer)

    x = Var("x", ListT(Int()))
    y = Var("y", ListT(Int()))
    mul_1d = FnDecl(MUL1D, ListT(Int()), mul_body(x, y), x, y)

    # checks that x and y have the same length
    def same_length_body(x, y):
        return Eq(ml_list_length(x), ml_list_length(y))

    same_length = FnDecl(SAME_LEN, Bool(), same_length_body(x, y), x, y)

    return [mul_1d, same_length]

basename = "mul1"
filename = "tests/mul1.ll"
fnName = "test"
loopsFile = "tests/mul1.loops"
cvcPath = "cvc5"

(vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

invAndPs = [grammar(ci) for ci in loopAndPsInfo]
lang = targetLang()

candidates = synthesize(basename, lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath)

def codeGen(summary: FnDecl):
    expr = summary.body() 
    def eval(expr):
        if isinstance(expr, Eq):
            return f"ans = {eval(expr.e2())}"
        elif isinstance(expr, Add):
            return f"{eval(expr.args[0])} + {eval(expr.args[1])}"
        elif isinstance(expr, Call):
            eval_args = []
            for a in expr.arguments():
                eval_args.append(eval(a))
            name = expr.name()
            return f"{name}({', '.join(eval_args)})"
        elif isinstance(expr, Lit):
            return str(expr.val())
        elif isinstance(expr, Tuple):
            eval_args = map(lambda expr: eval(expr), expr.args)
            return f"[{', '.join(eval_args)}]"
        else:
            return str(expr)
    return eval(expr)

for c in candidates:
    print(codeGen(c), "\n")
