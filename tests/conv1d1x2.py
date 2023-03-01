import shutil

from metalift.ir import *
from metalift.analysis import CodeInfo, analyze

from metalift.synthesize_auto import synthesize

MUL1D = "elementwise_mul"
SAME_LEN = "same_length"
CONV1D1X2 = "conv1d1x2"
DOTPROD2D = "dotprod_2d"

def ml_list_get(lst, i):
    return Call("list_get", Int(), lst, i)

def ml_list_head(lst):
    return ml_list_get(lst, IntLit(0))

def ml_list_tail(lst, i):
    return Call("list_tail", ListT(Int()), lst, i)

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

def ml_dotprod2d(x, y):
    return Call(DOTPROD2D, Int(), x, y)

def ml_conv1d1x2(vec, kernel):
    return Call(CONV1D1X2, ListT(Int()), vec, kernel)

def grammar(ci: CodeInfo):
    name = ci.name

    if name.startswith("inv"):
        raise Exception("Inv grammar unimplemented")
        # mV[0] is list, mV[1] is int
        print("INV VARS MV HERE")
        print(*ci.modifiedVars)
        print("INV VARS RV HERE")
        print(*ci.readVars)
        #some_input = ci.readVars[0]
        #other_input = ci.readVars[1]
        an_input = Choose(*ci.readVars)

        #prod = ci.modifiedVars[0]
        #i = ci.modifiedVars[1]
        #initial = Ge(i, IntLit(0))
        #                 #Gt(i, IntLit(0)),
        #                 #Le(i, IntLit(0)),
        #                 #Lt(i, IntLit(0)),
        #                 #Eq(i, IntLit(0)),
        #                 #Ge(i, IntLit(1)),
        #                 #Gt(i, IntLit(1)),
        #                 #Le(i, IntLit(1)),
        #                 #Lt(i, IntLit(1)),
        #                 #Eq(i, IntLit(1)))
        #loop_cond = Le(i, ml_list_length(some_input))
        #                   #Le(i, ml_list_length(an_input)),
        #                   #Gt(i, ml_list_length(an_input)),
        #                   #Ge(i, ml_list_length(an_input)),
        #                   #Eq(i, ml_list_length(an_input)))
        #post = Eq(prod, ml_mul1d(ml_list_take(some_input, i), ml_list_take(other_input, i)))
        #inv = And(initial, loop_cond)
        #summary = And(inv, post)
        summary = BoolLit(True)
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)
    else:
        output = ci.modifiedVars[0]
        (x, y) = ci.readVars
        # change this to Implies
        #summary = Implies(ml_same_len(x, y), Eq(ml_mul1d(x, y), output))
        summary = Eq(ml_conv1d1x2(x, y), output)
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)

def targetLang():
    x = Var("x", ListT(Int()))
    y = Var("y", ListT(Int()))

    # Ignores the rest of x if y is shorter
    def dotprod2d_body(x, y):
        element1 = Mul(ml_list_head(x), ml_list_head(y))
        x_rest = ml_list_tail(x, IntLit(1))
        y_rest = ml_list_tail(y, IntLit(1))
        element2 = Mul(ml_list_head(x_rest), ml_list_head(y_rest))
        return Add(element1, element2)
    dotprod2d = FnDeclNonRecursive(DOTPROD2D, Int(), dotprod2d_body(x, y), x, y)

    def conv1d1x2_body(vec, kernel):
        vec_size = ml_list_length(x)
        kernel_size = IntLit(2)
        cur_prod = ml_dotprod2d(vec, kernel)
        vec_rest = ml_list_tail(vec, IntLit(1))
        recursed = ml_conv1d1x2(vec_rest, kernel)
        general_answer = ml_list_prepend(cur_prod, recursed)
        return Ite(Eq(vec_size, kernel_size), ml_list_prepend(cur_prod, ml_list_empty()), general_answer)
    conv1d1x2 = FnDecl(CONV1D1X2, ListT(Int()), conv1d1x2_body(x, y), x, y)

    return [dotprod2d, conv1d1x2]

basename = "conv1d1x2"
filename = "tests/conv1d1x2.ll"
fnName = "test"
loopsFile = "tests/conv1d1x2.loops"
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
