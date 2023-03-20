from ast import arg
import os
import sys
from metalift.analysis import CodeInfo, analyze
from metalift.ir import *
from metalift.synthesize_rosette import synthesize
#from casper_synthesis import *

def filter_types(inp, inp_type):
    return list(filter(lambda x: parseTypeRef(x.type) == inp_type, inp))

def list_get(lst, i):
    return Call("list_get", Int(), lst, i)

def list_head(lst):
    return list_get(lst, IntLit(0))

def list_take(lst, i):
    return Call("list_take", ListT(Int()), lst, i)

def list_tail(lst, i):
    return Call("list_tail", ListT(Int()), lst, i)

def list_prepend(e, lst):
    return Call("list_prepend", ListT(Int()), e, lst)

def list_length(lst):
    return Call("list_length", Int(), lst)

def list_empty():
    return Call("list_empty", ListT(Int()))

def targetLang():
    arg1 = Var("arg1", ListT(Int()))
    arg2 = Var("arg2", ListT(Int()))
    multiply  = FnDecl("multiply",ListT(Int()),
                       Ite(Eq(list_length(arg1),IntLit(0)),
                           list_empty(),
                           list_prepend(Mul(list_get(arg1,IntLit(0)),
                                            list_get(arg2,IntLit(0))),
                                        Call("multiply",ListT(Int()),
                                             list_tail(arg1,IntLit(1)),
                                             list_tail(arg2,IntLit(1))))),
                       arg1,arg2)
    return [multiply]

def grammar(ci: CodeInfo):
    name = ci.name
    
    
    if name.startswith("inv"):
        intChoices = Choose(IntLit(0), IntLit(1))
        argChoices = Choose(*ci.readVars)
        for m in ci.modifiedVars:   
            print(m)
        # mV[1] is output (j)
        #index <= length(arg)
        i_1 = Choose(
            Ge(ci.modifiedVars[1], Call("list_length", Int(), ci.readVars[0])),
            Le(ci.modifiedVars[1], Call("list_length", Int(), ci.readVars[0])),
            Gt(ci.modifiedVars[1], Call("list_length", Int(), ci.readVars[0])),
            Lt(ci.modifiedVars[1], Call("list_length", Int(), ci.readVars[0])),
            Eq(ci.modifiedVars[1], Call("list_length", Int(), ci.readVars[0])),
        )
        # i>=0
        i_2 = Choose(
            Le(ci.modifiedVars[1], intChoices),
            Gt(ci.modifiedVars[1], intChoices),
            Ge(ci.modifiedVars[1], intChoices),
            Lt(ci.modifiedVars[1], intChoices),
            Eq(ci.modifiedVars[1], intChoices),
        )
        o = Choose(Eq(ci.modifiedVars[0], # output (c)
                      Call("multiply",
                           ListT(Int()),
                           list_take(argChoices,ci.modifiedVars[1]),
                           list_take(argChoices,ci.modifiedVars[1]))))
        e = And(o,And(i_1,i_2))
        return Synth(ci.name, e, *ci.modifiedVars, *ci.readVars)

    elif name.startswith("test"):  # ps
        argChoices = Choose(*ci.readVars)
        choices = Choose(Eq(ci.modifiedVars[0], Call("multiply",ListT(Int()),argChoices,argChoices)))
        return Synth(name, choices, *ci.modifiedVars, *ci.readVars)
    else:
        raise Exception(f"Unknown function {name}")



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
            if name == "multiply":
                # Do not call multiply recursively
                name = "np.multiply"
                args = expr.arguments()
                assert(len(args) == 2)
                M = f"np.array([{eval(args[0])}, {eval(args[1])}]).T"
                x = eval(args[2])
                return f"{name}({M}, {x})"
            return f"{name}({', '.join(eval_args)})"
        elif isinstance(expr, Lit):
            return str(expr.val())
        elif isinstance(expr, Tuple):
            eval_args = map(lambda expr: eval(expr), expr.args)
            return f"[{', '.join(eval_args)}]"
        else:
            return str(expr)
    return eval(expr)


if __name__ == "__main__":

    #filename = "tests/mul1.ll"
    #basename = "mul1"

    #fnName = "test"
    #loopsFile = "tests/mul1.loops"
    #cvcPath = "cvc5"
    filename = "tests/element-wise-inner.ll"
    basename = "element-wise-inner"

    fnName = "test"
    loopsFile = "tests/element-wise-inner.loops"
    cvcPath = "cvc5"

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)
    print('===== vc', vc)
    print("====== synthesis")
    invAndPs = [grammar(ci) for ci in loopAndPsInfo]

    lang = targetLang()

    candidates = synthesize(
        basename,
        lang,
        vars,
        invAndPs,
        preds,
        vc,
        loopAndPsInfo,
        cvcPath,
    )
    print("====== verified candidates")
    for c in candidates:
        print(codeGen(c), "\n")
