import shutil

from metalift.ir import *
from metalift.analysis import CodeInfo, analyze

from metalift.synthesize_auto import synthesize

MUL1D = "elementwise_mul"
SAME_LEN = "same_length"
CONV1D1XN = "conv1d1xn"
DOTPRODND = "dotprod_nd"

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

def ml_dotprodnd(x, y):
    return Call(DOTPRODND, Int(), x, y)

def ml_conv1d1xn(vec, kernel):
    return Call(CONV1D1XN, ListT(Int()), vec, kernel)

def grammar(ci: CodeInfo):
    name = ci.name

    if name.startswith("inv"):
        # mV[0] is list, mV[1] is int
        print("INV VARS MV HERE")
        print(*ci.modifiedVars)
        print("INV VARS RV HERE")
        print(*ci.readVars)
        an_input = Choose(*ci.readVars)
        #an_output = Choose(*ci.modifiedVars)
        #an_output_i32 = Choose(ci.modifiedVars[0], ci.modifiedVars[1], ci.modifiedVars[2], ci.modifiedVars[4])
        #an_output_list = ci.modifiedVars[3]
        an_output_i32 = ci.modifiedVars[1]
        an_output_list = ci.modifiedVars[0]

        #initial = Choose(Ge(an_output_i32, IntLit(0)),
        #                 Gt(an_output_i32, IntLit(0)),
        #                 Le(an_output_i32, IntLit(0)),
        #                 Lt(an_output_i32, IntLit(0)),
        #                 Eq(an_output_i32, IntLit(0)),
        #                 Ge(an_output_i32, IntLit(1)),
        #                 Gt(an_output_i32, IntLit(1)),
        #                 Le(an_output_i32, IntLit(1)),
        #                 Lt(an_output_i32, IntLit(1)),
        #                 Eq(an_output_i32, IntLit(1)))
        #initial2 = Choose(Le(an_output_i32, ml_list_length(an_input)),
        #                   Lt(an_output_i32, ml_list_length(an_input)),
        #                   Ge(an_output_i32, ml_list_length(an_input)),
        #                   Gt(an_output_i32, ml_list_length(an_input)),
        #                   Eq(an_output_i32, ml_list_length(an_input)))
        #preloop = And(initial, initial2)
        #conv = an_output_list
        #take_idx = Choose(an_output_i32, Sub(an_output_i32, IntLit(1)), Add(an_output_i32, IntLit(1)))
        #post = Eq(conv, ml_conv1d1xn(ml_list_take(an_input, an_output_i32), an_input))
        #summary = And(preloop, post)

        preloop = Ge(an_output_i32, IntLit(0))
        postloop = Le(an_output_i32, Sub(ml_list_length(an_input), IntLit(1)))
        inductive = Eq(an_output_list, ml_co)
        summary = Implies(Gt(ml_list_length(an_input), IntLit(1)), And(preloop, And(postloop, inductive)))

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
        #summary = BoolLit(True)
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)
    else:
        output = ci.modifiedVars[0]
        x = ci.readVars[0]
        unknown_const = Choose(IntLit(0), IntLit(1), IntLit(2), IntLit(3))
        y = ml_list_prepend(unknown_const, ml_list_prepend(unknown_const, ml_list_empty()))
        # change this to Implies
        #summary = Implies(ml_same_len(x, y), Eq(ml_mul1d(x, y), output))
        summary = Eq(ml_conv1d1xn(x, y), output)
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)

def targetLang(n):
    x = Var("x", ListT(Int()))
    y = Var("y", ListT(Int()))

    # Ignores the rest of x if y is shorter
    def dotprodnd_body(x, y, n):
        element1 = Mul(ml_list_head(x), ml_list_head(y))
        x_rest = ml_list_tail(x, IntLit(1))
        y_rest = ml_list_tail(y, IntLit(1))
        rest = dotprodnd_body(x_rest, y_rest, n-1)
        if n == 0:
            return element1
        return Add(element1, rest)
    dotprodnd = FnDeclNonRecursive(DOTPRODND, Int(), dotprodnd_body(x, y, n), x, y)

    def conv1d1xn_body(vec, kernel):
        nonlocal n
        vec_size = ml_list_length(x)
        kernel_size = IntLit(n)
        cur_prod = ml_dotprodnd(vec, kernel)
        vec_rest = ml_list_tail(vec, IntLit(1))
        recursed = ml_conv1d1xn(vec_rest, kernel)
        general_answer = ml_list_prepend(cur_prod, recursed)
        return Ite(Eq(vec_size, kernel_size), ml_list_prepend(cur_prod, ml_list_empty()), general_answer)
    conv1d1xn = FnDecl(CONV1D1XN, ListT(Int()), conv1d1xn_body(x, y), x, y)

    return [dotprodnd, conv1d1xn]

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
            if name == CONV1D1XN:
                name = "torch.nn.functional.conv1d"
                args = expr.arguments()
                assert(len(args) == 2)
                input = f"torch.tensor({args[0]})"
                kernel = f"torch.tensor({args[1]})"
                return f"{name}({input}, {kernel})"
            return f"{name}({', '.join(eval_args)})"
        elif isinstance(expr, Lit):
            return str(expr.val())
        elif isinstance(expr, Tuple):
            eval_args = map(lambda expr: eval(expr), expr.args)
            return f"[{', '.join(eval_args)}]"
        else:
            return str(expr)
    return eval(expr)

def runner(n):
    basename = "conv1d1x2"
    filename = "tests/conv1d1x2.ll"
    fnName = "test"
    loopsFile = "tests/conv1d1x2.loops"
    cvcPath = "cvc5"
    
    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)
    
    invAndPs = [grammar(ci) for ci in loopAndPsInfo]
    lang = targetLang(n)
    
    # TODO: noVerify=True, increase listBound for bounded verification
    candidates = synthesize(basename, lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath)
    
    for c in candidates:
        print(codeGen(c), "\n")

successful_synthesis = False
n = 1
while not successful_synthesis:
    try:
        runner(n)
        successful_synthesis = True
    except:
        successful_synthesis = False
        n += 1
