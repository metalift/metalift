from ast import arg
import os
import sys
from metalift.analysis import CodeInfo, analyze
from metalift.ir import *
from metalift.synthesize_rosette import synthesize
from casper_synthesis import *

def filter_types(inp, inp_type):
    return list(filter(lambda x: parseTypeRef(x.type) == inp_type, inp))

def targetLang():
    arg1 = Var("arg1", ListT(Int()))
    arg2 = Var("arg2", ListT(Int()))
    multiply  = FnDecl("multiply",ListT(Int()),Ite(Eq(list_length(arg1),IntLit(0)),list_empty(),list_prepend(Mul(list_get(arg1,IntLit(0)), list_get(arg2,IntLit(0))),Call("multiply",ListT(Int),list_tail(arg1,IntLit(1)),list_tail(arg2,IntLit(1))))),arg1,arg2)
    return [multiply]

def grammar(ci: CodeInfo):
    name = ci.name
    
    
    if name.startswith("inv"):
        intChoices = Choose(IntLit(0), IntLit(1))
        argChoices = Choose(*ci.readVars)
        for m in ci.modifiedVars:   
            print(m)
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
        o = Choose(Eq(ci.modifiedVars[0],Call("multiply",ListT(Int()),list_take(argChoices,ci.modifiedVars[1]),list_take(argChoices,ci.modifiedVars[1]))))
        e = And(o,And(i_1,i_2))
        return Synth(ci.name, e, *ci.modifiedVars, *ci.readVars)

    elif name.startswith("test"):  # ps
        argChoices = Choose(*ci.readVars)
        choices = Choose(Eq(ci.modifiedVars[0], Call("multiply",ListT(Int),argChoices,argChoices)))
        return Synth(name, choices, *ci.modifiedVars, *ci.readVars)
    else:
        raise Exception(f"Unknown function {name}")






if __name__ == "__main__":

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
    # print("====== verified candidates")
    # for c in candidates:
    #     print(c, "\n")