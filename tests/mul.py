import shutil

from metalift.ir import *
from metalift.transpiler import Transpiler
from metalift.analysis import CodeInfo, analyze

from metalift.synthesize_auto import synthesize

MUL_EQUAL = "elementwise_mul"
LEN_CHECK = "length_check"
DOT_PROD = "dot_product"
CONV_1D = "conv1d"

def ml_list_get(lst, i):
    return Call("list_get", Int(), lst, i)

def ml_list_head(lst):
    return ml_list_get(lst, IntLit(0))

def ml_list_tail(lst):
    return Call("list_tail", ListT(Int()), lst)

def ml_list_length(lst):
    return Call("list_length", Int(), lst)

def ml_min(a, b):
    return Ite(Lt(a, b), a, b)

def grammar(ci: CodeInfo):
    name = ci.name

    prod = ci.modifiedVars[0]
    (x, y) = ci.readVars
    # change this to Implies
    summary = And(Call(LEN_CHECK, Bool(), prod, x, y), Call(MUL_EQUAL, Bool(), prod, x, y))
    return Synth(name, summary, *ci.modifiedVars, *ci.readVars)

def targetLang():
    def mul_equal_body(prod, x, y):
        size = ml_min(ml_list_length(x), ml_list_length(y))
        cur_output_prod = ml_list_head(prod)
        cur_input_prod = Mul(ml_list_head(x), ml_list_head(y))
        prod_rest = ml_list_tail(prod)
        x_rest = ml_list_tail(x)
        y_rest = ml_list_tail(y)
        recursed = Call(MUL_EQUAL, Bool(), prod_rest, x_rest, y_rest)
        # fix this, avoid using Ite (replace w Implies)
        return Ite(Eq(size, IntLit(0)), BoolLit(True), And(Eq(cur_output_prod, cur_input_prod), recursed))

    prod = Var("prod", ListT(Int()))
    x = Var("x", ListT(Int()))
    y = Var("y", ListT(Int()))
    mul_equal = FnDecl(MUL_EQUAL, Bool(), mul_equal_body(prod, x, y), prod, x, y)

    # checks that length of output is equal to the smaller of x and y
    def length_check_body(output, x, y):
        correct_size = ml_min(ml_list_length(x), ml_list_length(y))
        output_size = ml_list_length(output)
        return Eq(output_size, correct_size)

    output = Var("output", ListT(Int()))
    length_check = FnDecl(LEN_CHECK, Bool(), length_check_body(output, x, y), output, x, y)

    def dot_product_body(x, y):
        size = ml_min(ml_list_length(x), ml_list_length(y))
        cur_elem_prod = Mul(ml_list_head(x), ml_list_head(y))
        x_rest = ml_list_tail(x)
        y_rest = ml_list_tail(y)
        return Ite(Eq(size, IntLit(0)), IntLit(0), Add(cur_elem_prod, Call(DOT_PROD, Int(), x_rest, y_rest)))
    output = Var("dprod", Int())
    dot_product = FnDecl(DOT_PROD, Int(), dot_product_body(x, y), output, x, y)

    def conv1d_equal_body(conv, x, kernel):
        remaining_size = ml_list_length(conv)
        cur_output_elem = ml_list_head(conv)
        cur_input_elem = Call(DOT_PROD, Int(), x, kernel)
        conv_rest = ml_list_tail(conv)
        x_rest = ml_list_tail(x)
        return Ite(Eq(remaining_size, IntLit(0)),
                   BoolLit(True),
                   And(Eq(cur_output_elem, cur_input_elem), Call(CONV_1D, Bool(), conv_rest, x_rest, kernel)))
    output = Var("conv", ListT(Int()))
    conv1d_equal = FnDecl(CONV_1D, ListT(Int()), conv1d_equal_body(output, x, y), output, x, y)


    return [mul_equal, length_check, dot_product, conv1d_equal]

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
