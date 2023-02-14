import os
import sys

from metalift.analysis import CodeInfo, analyze
from metalift.ir import *
from metalift.rosette_translator import toRosette
from metalift.smt_util import toSMT

from metalift.synthesize_auto import synthesize

def call_mat_mul(a, b, x):
    return Call("mat_mul", TupleT(Int(), Int()), a, b, x)

def call_not_l2_norm(p):
    return Call("not_l2_norm", Int(), p)

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
    not_l2_norm_p = call_not_l2_norm(p) 
    # this is a wrong answer
    not_l2_norm_wrong_p = call_not_l2_norm(wrong_p) 
    # this is a wrong answer
    not_l2_norm_wrong_p2 = call_not_l2_norm(wrong_p2)

    summary = Eq(r, Choose(not_l2_norm_p, not_l2_norm_wrong_p, not_l2_norm_wrong_p2))
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
    not_l2_norm = FnDecl(
        "not_l2_norm", Int(), Add(Add(p0, p0), Add(p1, p1)), p
    )
    return [mat_mul, not_l2_norm]

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
      if name == "mat_mul":
        name = "np.matmul"
      elif name == "not_l2_norm":
        name == "2 * np.sum"
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
