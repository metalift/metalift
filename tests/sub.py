from metalift.analysis_new import VariableTracker
from metalift.analysis import analyze
from metalift.ir import *

from metalift.synthesize_auto import synthesize

def negate(a):
    return Call("negate", Int(), a)

def subtract(a, b):
    return Call("subtract", Int(), a, b)

def grammar(ci):
    name = ci.name
    r = ci.modifiedVars[0]
    (x, y) = ci.readVars
    summary = Eq(r, Sub(x, Choose(y, Sub(IntLit(0), y))))
    return Synth(name, summary, *ci.modifiedVars, *ci.readVars)

def targetLang():
    a = Var("a", Int())
    x = Var("x", Int())
    y = Var("y", Int())
    negate = FnDecl("negate", Int(), Sub(IntLit(0), a), a)
    subtract = FnDecl("subtract", Int(), Sub(x, y), x, y)
    return [negate, subtract]

filename = "tests/sub.ll"
basename = "sub"

fnName = "test"

loopsFile = "tests/sub.loops"

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
