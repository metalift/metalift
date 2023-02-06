import os
import sys

from metalift.analysis import CodeInfo, analyze
from metalift.ir import *
from metalift.rosette_translator import toRosette
from metalift.smt_util import toSMT

from metalift.synthesize_auto import synthesize

def call_mat_mul(a, b, x):
    return Call("mat_mul", TupleT(Int(), Int()), a, b, x)

def call_l2_norm(p):
    return Call("l2_norm", Int(), p)

def grammar(ci: CodeInfo):
    name = ci.name

    r = ci.modifiedVars[0]
    (a0, a1, b0, b1, x0, x1) = ci.readVars
    # Calculate the squared L2 norm
    a = Tuple(a0, a1)
    b = Tuple(b0, b1)
    x = Tuple(x0, x1)
    p = call_mat_mul(a, b, x)
    wrong_p = call_mat_mul(b, a, x)
    wrong_p2 = call_mat_mul(a, x, b)

    l2_norm_p = call_l2_norm(p)
    l2_norm_wrong_p = call_l2_norm(wrong_p)
    l2_norm_wrong_p2 = call_l2_norm(wrong_p2)

    #summary = Eq(r, Choose(l2_norm_p, l2_norm_wrong_p, l2_norm_wrong_p2))
    summary = Eq(r, l2_norm_p)
    return Synth(name, summary, *ci.modifiedVars, *ci.readVars)

def targetLang():
    a = Var("a", TupleT(Int(), Int()))
    b = Var("b", TupleT(Int(), Int()))
    x = Var("x", TupleT(Int(), Int()))
    def make_mat_mul_fnbody(a, b, x):
        p0l = Mul(TupleGet(a, IntLit(0)), TupleGet(x, IntLit(0)))
        p0r = Mul(TupleGet(b, IntLit(0)), TupleGet(x, IntLit(1)))
        p1l = Mul(TupleGet(a, IntLit(1)), TupleGet(x, IntLit(0)))
        p1r = Mul(TupleGet(b, IntLit(1)), TupleGet(x, IntLit(1)))
        return Tuple(Add(p0l, p0r), Add(p1l, p1r))
    mat_mul = FnDecl(
        "mat_mul", TupleT(Int(), Int()), make_mat_mul_fnbody(a, b, x), a, b, x
    )
    p = Var("p", TupleT(Int(), Int()))
    p0 = TupleGet(p, IntLit(0))
    p1 = TupleGet(p, IntLit(1))
    l2_norm = FnDecl(
        "l2_norm", Int(), Add(Mul(p0, p0), Mul(p1, p1)), p
    )
    return [mat_mul, l2_norm]

basename = "mat1"
filename = "tests/mat1.ll"
fnName = "test"
loopsFile = "tests/mat1.loops"
cvcPath = "cvc5"

(vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

invAndPs = [grammar(ci) for ci in loopAndPsInfo]
lang = targetLang()

candidates = synthesize(basename, lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath)

def codeGen(summary: FnDecl):
  expr = summary.body() 
  def eval(expr):
    if isinstance(expr, Eq):
      return f"{expr.e1()} = {eval(expr.e2())}"
    elif isinstance(expr, Add):
      return f"{eval(expr.args[0])} + {eval(expr.args[1])}"
    elif isinstance(expr, Call):
      eval_args = []
      for a in expr.arguments():
        eval_args.append(eval(a))
      return f"{expr.name()}({', '.join(eval_args)})"
    elif isinstance(expr, Lit):
      return str(expr.val())
    else:
      return str(expr)
  return eval(expr)

summary = codeGen(candidates[0])

print(summary)
