import shutil

# modified runner to check larger arrays

from metalift.ir import *
from metalift.analysis import CodeInfo, analyze
from metalift.synthesis_common import SynthesisFailed

from metalift.synthesize_auto import synthesize

MUL1D = "elementwise_mul"
SAME_LEN = "same_length"
CONV1D1X2 = "conv1d1x2"
DOTPROD2D = "dotprod_2d"
DOTPROD = "dotprod"

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

def ml_dotprod(x, y):
    return Call(DOTPROD, Int(), x, y)

def ml_conv1d1x2(vec, kernel):
    return Call(CONV1D1X2, ListT(Int()), vec, kernel)

def grammar(ci: CodeInfo):
    name = ci.name

    print("INV VARS MV HERE")
    print(*ci.modifiedVars)
    print("INV VARS RV HERE")
    print(*ci.readVars)

    if name.startswith("inv"):
        # mV[0] is list, mV[1] is int

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
        #post = Eq(conv, ml_conv1d1x2(ml_list_take(an_input, an_output_i32), an_input))
        #summary = And(preloop, post)

        valid = Gt(ml_list_length(an_input), IntLit(1))
        preloop = Ge(an_output_i32, IntLit(0))
        postloop = Le(an_output_i32, Sub(ml_list_length(an_input), IntLit(1)))
        induction = Eq(an_output_list, ml_conv1d1x2(ml_list_take(an_input, Add(an_output_i32, IntLit(1))), ml_list_prepend(IntLit(1), ml_list_prepend(IntLit(1), ml_list_empty()))))
        # TODO: replace implies w equivalent
        summary = Implies(valid, And(preloop, And(postloop, induction)))

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
        an_input = ci.readVars[0]
        an_output = Choose(*ci.modifiedVars)
        x = ci.readVars[0]
        unknown_const = Choose(IntLit(0), IntLit(5), IntLit(2), IntLit(3))
        y = ml_list_prepend(unknown_const, ml_list_prepend(unknown_const, ml_list_empty()))
        # change this to Implies
        #summary = Implies(ml_same_len(x, y), Eq(ml_mul1d(x, y), output))
        #summary = Eq(ml_conv1d1x2(x, y), output)
        valid = Gt(ml_list_length(x), IntLit(1))
        ans = ml_conv1d1x2(an_input, y)
        check_ans = Eq(ans, an_output)
        # Note: Grammar should always return boolean value; compare w OUT to check answer
        # The answer expression should always be of the form Eq(out, ...)
        # Wrong:
        #summary = Ite(valid, check_ans, ml_list_empty())
        # Correct:
        summary = Implies(valid, check_ans)
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)

def targetLang(kernel_size=2):
    x = Var("x", ListT(Int()))
    y = Var("y", ListT(Int()))

    # Ignores the rest of x if y is shorter
    # TODO: just take idx 1
    def dotprod2d_body(x, y):
        element1 = Mul(ml_list_head(x), ml_list_head(y))
        x_rest = ml_list_tail(x, IntLit(1))
        y_rest = ml_list_tail(y, IntLit(1))
        element2 = Mul(ml_list_head(x_rest), ml_list_head(y_rest))
        return Add(element1, element2)
    dotprod2d = FnDeclNonRecursive(DOTPROD2D, Int(), dotprod2d_body(x, y), x, y)

    def dotprod_body(x, y):
        kernel_size = ml_list_length(y)
        cur_prod = Mul(ml_list_head(x), ml_list_head(y))
        x_rest = ml_list_tail(x, IntLit(1))
        y_rest = ml_list_tail(y, IntLit(1))
        recursed = ml_dotprod(x_rest, y_rest)
        return Ite(Lt(kernel_size, IntLit(2)), cur_prod, Add(cur_prod, recursed))
    dotprod = FnDecl(DOTPROD, Int(), dotprod_body(x, y))

    # TODO: handle input size < 2
    # TODO: for size < 2, don't call dotprod
    def conv1d1x2_body(vec, kernel):
        nonlocal kernel_size
        vec_size = ml_list_length(x)
        kernel_size = IntLit(kernel_size)
        cur_prod = ml_dotprod(vec, kernel)
        vec_rest = ml_list_tail(vec, IntLit(1))
        recursed = ml_conv1d1x2(vec_rest, kernel)
        general_answer = ml_list_prepend(cur_prod, recursed)
        #return Ite(Eq(vec_size, kernel_size), ml_list_prepend(cur_prod, ml_list_empty()), general_answer)
        return Ite(Lt(vec_size, kernel_size), ml_list_empty(), general_answer)
    conv1d1x2 = FnDecl(CONV1D1X2, ListT(Int()), conv1d1x2_body(x, y), x, y)

    return [dotprod2d, dotprod, conv1d1x2]

def codeGen(summary: FnDecl):
    def eval(expr):
        if isinstance(expr, Eq):
            return f"ans = {eval(expr.e2())}"
        elif isinstance(expr, Gt):
            left = expr.args[0]
            right = expr.args[1]
            return f"({eval(left)}) > ({eval(right)})"
        elif isinstance(expr, Add):
            return f"{eval(expr.args[0])} + {eval(expr.args[1])}"
        elif isinstance(expr, FnDecl):
            return f"def {expr.name()}({', '.join([eval(arg) for arg in expr.arguments()])}):\n    " \
                    f"return {eval(expr.body())}"
        elif isinstance(expr, Call):
            eval_args = []
            for a in expr.arguments():
                eval_args.append(eval(a))
            name = expr.name()
            if name == CONV1D1X2:
                name = "torch.nn.functional.conv1d"
                args = expr.arguments()
                assert(len(args) == 2)
                input = f"torch.tensor({args[0]})"
                kernel = f"torch.tensor({args[1]})"
                return f"{name}({input}, {kernel})"
            return f"{name}({', '.join(eval_args)})"
        elif isinstance(expr, Lit):
            return str(expr.val())
        elif isinstance(expr, Var):
            return expr.name()
        elif isinstance(expr, Tuple):
            eval_args = map(lambda expr: eval(expr), expr.args)
            return f"[{', '.join(eval_args)}]"
        elif isinstance(expr, Implies):
            left = expr.args[0]
            right = expr.args[1]
            return f"not ({eval(left)}) or ({eval(right)})"
        else:
            print(type(expr))
            return str(expr)
    return eval(summary)

def runner():
    basename = "conv1d1x2"
    filename = "tests/conv1d1x2.ll"
    fnName = "test"
    loopsFile = "tests/conv1d1x2.loops"
    cvcPath = "cvc5"

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

    invAndPs = [grammar(ci) for ci in loopAndPsInfo]
    lang = targetLang()

    # noVerify=True is OK, since synthesis will not create a candidate for kernel that's too small
    candidates = []
    try:
        candidates = synthesize(basename, lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath, noVerify=True)
    except SynthesisFailed:
        print("Synthesis failed")
    except:
        print("unexpected error")

    for c in candidates:
        if c.args[0] != "test":
            continue
        print(c.args[0])
        #print(c)
        print(codeGen(c), "\n")

runner()
