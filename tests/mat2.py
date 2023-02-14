import os
import sys

from metalift.analysis import CodeInfo, analyze
from metalift.ir import *
from metalift.rosette_translator import toRosette
from metalift.smt_util import toSMT

from metalift.synthesize_auto import synthesize

L1_NORM = "l1_norm"
MAT_MUL = "mat_mul"

def call_mat_mul(a, b, x):
    return Call(MAT_MUL, TupleT(Int(), Int()), a, b, x)

def call_l1_norm(p):
    return Call(L1_NORM, Int(), p)

def grammar(ci: CodeInfo):
    name = ci.name

    r = ci.modifiedVars[0]
    (a0, a1, b0, b1, x0, x1) = ci.readVars
    # Calculate the matrix-vector product
    a = Tuple(a0, a1)
    b = Tuple(b0, b1)
    x = Tuple(x0, x1)
    p = call_mat_mul(a, b, x)
    wrong_p = call_mat_mul(b, a, x)
    wrong_p2 = call_mat_mul(a, x, b)

    # this is the correct answer
    l1_norm_p = call_l1_norm(p) 
    # this is a wrong answer
    l1_norm_wrong_p = call_l1_norm(wrong_p) 
    # this is a wrong answer
    l1_norm_wrong_p2 = call_l1_norm(wrong_p2)

    summary = Eq(r, Choose(l1_norm_p, l1_norm_wrong_p, l1_norm_wrong_p2))
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
        MAT_MUL, TupleT(Int(), Int()), make_mat_mul_fnbody(a, b, x), a, b, x
    )
    p = Var("p", TupleT(Int(), Int()))
    def make_l1_norm_fnbody(p):
        p0 = TupleGet(p, IntLit(0))
        p1 = TupleGet(p, IntLit(1))
        p0_abs = Ite(Lt(p0, IntLit(0)), Sub(IntLit(0), p0), p0)
        p1_abs = Ite(Lt(p1, IntLit(0)), Sub(IntLit(0), p1), p1)
        return Add(p0_abs, p1_abs)
    l1_norm = FnDecl(
        L1_NORM, Int(), make_l1_norm_fnbody(p), p
    )
    return [mat_mul, l1_norm]

basename = "mat2"
filename = "tests/mat2.ll"
fnName = "test"
loopsFile = "tests/mat2.loops"
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
      if name == MAT_MUL:
        name = "np.matmul"
      elif name == L1_NORM:
        name = "2 * np.sum"
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
