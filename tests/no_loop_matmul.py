import os
import shutil
import sys

from metalift.analysis import CodeInfo, analyze
from metalift.ir import *
from metalift.rosette_translator import toRosette
from metalift.smt_util import toSMT

from metalift.synthesize_auto import synthesize
from metalift.transpiler import Transpiler

L1_NORM = "l1_norm"
MAT_MUL = "mat_mul"

Lit.codegen = lambda self: self.val()
Var.codegen = lambda self: self.name()
Add.codegen = lambda self: f'{" + ".join([str(a.codegen()) for a in self.args])}'
FnDeclRecursive.codegen = lambda self: f'def {self.name()}({", ".join([str(a.codegen()) for a in self.arguments()])}):\n  ' \
        f'return {self.body().codegen()}'
Tuple.codegen = lambda self: f"[{', '.join(map(lambda arg: arg.codegen(), self.args))}]"

def targetLang():
    def make_mat_mul_fnbody(a, b, x):
        p0l = Mul(TupleGet(a, IntLit(0)), TupleGet(x, IntLit(0)))
        p0r = Mul(TupleGet(b, IntLit(0)), TupleGet(x, IntLit(1)))
        p1l = Mul(TupleGet(a, IntLit(1)), TupleGet(x, IntLit(0)))
        p1r = Mul(TupleGet(b, IntLit(1)), TupleGet(x, IntLit(1)))
        return Tuple(Add(p0l, p0r), Add(p1l, p1r))
    def mat_mul_codegen(a, b, x):
        M = f"np.array([{a.codegen()}, {b.codegen()}]).T"
        x = x.codegen()
        return f"np.matmul({M}, {x})"
    mat_mul = Target(MAT_MUL, [TupleT(Int(), Int()), TupleT(Int(), Int()), TupleT(Int(), Int())], TupleT(Int(), Int()),
                     lambda a, b, x: make_mat_mul_fnbody(a, b, x),
                     mat_mul_codegen)
    def make_l1_norm_fnbody(p):
        p0 = TupleGet(p, IntLit(0))
        p1 = TupleGet(p, IntLit(1))
        p0_abs = Ite(Lt(p0, IntLit(0)), Sub(IntLit(0), p0), p0)
        p1_abs = Ite(Lt(p1, IntLit(0)), Sub(IntLit(0), p1), p1)
        return Add(p0_abs, p1_abs)
    l1_norm = Target(L1_NORM, [TupleT(Int(), Int())], Int(),
                     lambda p: make_l1_norm_fnbody(p),
                     lambda p: f"np.linalg.norm({p.codegen()}, ord=1)")
    return [mat_mul, l1_norm]

def grammar(readVars, retVal, isLoop):
    mat_mul, l1_norm = targetLang()
    (a0, a1, b0, b1, x0, x1) = readVars
    # Calculate the matrix-vector product
    a = Tuple(a0, a1)
    b = Tuple(b0, b1)
    x = Tuple(x0, x1)
    p = mat_mul.call(a, b, x)
    wrong_p = mat_mul.call(b, a, x)
    wrong_p2 = mat_mul.call(a, x, b)

    # this is the correct answer
    l1_norm_p = l1_norm.call(p) 
    # this is a wrong answer
    l1_norm_wrong_p = l1_norm.call(wrong_p) 
    # this is a wrong answer
    l1_norm_wrong_p2 = l1_norm.call(wrong_p2)

    answerGrammar = Choose(l1_norm_p, l1_norm_wrong_p, l1_norm_wrong_p2)
    rv = NonTerm(Int(), isStart=True)
    return {rv: answerGrammar}

def runner():
    t = Transpiler(grammar, cvcPath=shutil.which("cvc5"))
    r = t.transpile("tests/no_loop_matmul.ll", "test")

    code = \
"""
import numpy as np
""" + \
    r.codegen() + \
"""
print(test(1, 3, 2, 4, 5, 6)) # 56

# # Correct answer:
# import numpy as np
# def test(arg, arg1, arg2, arg3, arg4, arg5):
#     return np.linalg.norm(np.matmul(np.array([[arg, arg1], [arg2, arg3]]).T, [arg4, arg5]), ord=1)
"""

    print(code)
    #exec(code, globals())

runner()
