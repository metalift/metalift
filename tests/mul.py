import shutil

from metalift.ir import *
from metalift.transpiler import Transpiler
from metalift.analysis import CodeInfo, analyze

from metalift.synthesize_auto import synthesize

def ml_list_get(lst, i):
    return Call("list_get", Int(), lst, i)

def ml_list_head(lst):
    return ml_list_get(lst, IntLit(0))

def ml_list_length(lst):
    return Call("list_length", Int(), lst)

def ml_min(a, b):
    return Ite(Lt(a, b), a, b)

def mul_semantic_bounded(prod, x, y, depth):
    if depth == 0:
        return BoolLit(True)
    size = ml_min(ml_list_length(x), ml_list_length(y))
    cur_output_prod = ml_list_head(prod)
    cur_input_prod = Mul(ml_list_head(x), ml_list_head(y))
    prod_rest = Call("list_tail", ListT(Int()), prod, IntLit(1))
    x_rest = Call("list_tail", ListT(Int()), x, IntLit(1))
    y_rest = Call("list_tail", ListT(Int()), y, IntLit(1))
    recursed = mul_semantic_bounded(prod_rest, x_rest, y_rest, depth - 1)
    return Or(Eq(size, IntLit(0)), And(Eq(cur_output_prod, cur_input_prod), recursed))

def mul_semantic(prod, x, y):
    size = ml_min(ml_list_length(x), ml_list_length(y))
    cur_output_prod = ml_list_head(prod)
    cur_input_prod = Mul(ml_list_head(x), ml_list_head(y))
    prod_rest = Call("list_tail", ListT(Int()), prod)
    x_rest = Call("list_tail", ListT(Int()), x)
    y_rest = Call("list_tail", ListT(Int()), y)
    recursed = mul_semantic(prod_rest, x_rest, y_rest)
    return Or(Eq(size, IntLit(0)), And(Eq(cur_output_prod, cur_input_prod), recursed))

def grammar(ci: CodeInfo):
    name = ci.name

    prod = ci.modifiedVars[0]
    (x, y) = ci.readVars
    #summary = mul_semantic(prod, x, y)
    summary = mul_semantic_bounded(prod, x, y, 3)
    return Synth(name, summary, *ci.modifiedVars, *ci.readVars)

def targetLang():
    return []

basename = "mul"
filename = "tests/mul.ll"
fnName = "test"
loopsFile = "tests/mul.loops"
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

summary = codeGen(candidates[0])

print(summary)
