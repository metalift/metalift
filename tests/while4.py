import os
import sys

from analysis import CodeInfo, analyze
from ir import Choose, And, Ge, Eq, Le, Sub, Synth, Call, Int, IntLit, Or, FnDecl, Var, Add, Ite
from synthesis import synthesize_new


# # programmatically generated grammar
def grammar(ci: CodeInfo):
  name = ci.name

  if name.startswith("inv"):
    e = Choose(*ci.modifiedVars)
    f = Choose(IntLit(1), IntLit(2), IntLit(3))
    c = Eq(e, Call("sum_n", Int(), Sub(e, f)))
    d = And(Ge(e, f), Le(e, f))
    b = And(c, d)
    return Synth(ci.name, b, *ci.modifiedVars, *ci.readVars)

    # (synth-fun inv0 ((tmp Int) (tmp1 Int) ) Bool
    #    ((B Bool) (C Bool) (D Bool) (E Int) (F Int))
    #    ((B Bool ((and C D)))
    #    (C Bool ((= E (sum_n (- E F)))))
    #    (D Bool ((and (>= E F) (<= E F))))
    #    (E Int (tmp tmp1))
    #    (F Int (1 2 3))))

  else:  # ps
    rv = ci.modifiedVars[0]
    choices = Choose(IntLit(1), IntLit(2))
    b = Eq(rv, Call("sum_n", Int(), choices))
    return Synth(name, b, *ci.modifiedVars, *ci.readVars)

    # (synth-fun ps ( (tmp12 Int) ) Bool
    #  ((B Bool) (C Int) (D Int))
    #  ((B Bool ((= C (sum_n D))))
    #  (C Int (tmp12))
    #  (D Int (1 2))))


# sum_n (x : int):
#   if x >= 1: return x + sum_n(x - 1)
#   else: return 0
def targetLang():
  x = Var("x", Int())
  sum_n = FnDecl("sum_n", Int(), Ite(Ge(x, IntLit(1)), Add(x, Call("sum_n", Int(), Sub(x, IntLit(1)))), IntLit(0)), x)
  return [sum_n]


if __name__ == "__main__":
  filename = sys.argv[1]
  basename = os.path.splitext(os.path.basename(filename))[0]

  fnName = sys.argv[2]
  loopsFile = sys.argv[3]
  cvcPath = sys.argv[4]

  (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

  print("====== synthesis")
  invAndPs = [grammar(ci) for ci in loopAndPsInfo]

  lang = targetLang()

  candidates = synthesize_new(lang, invAndPs, vars, preds, vc, cvcPath, basename)


