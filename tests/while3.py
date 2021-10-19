import os
import sys

from analysis import CodeInfo, analyze
from ir import Choose, And, Ge, Eq, Le, Sub, Synth, Call, Int, IntLit, Or, FnDecl, Var, Add, Ite
from synthesize_rosette import synthesize
from rosette_translator import toRosette

# # programmatically generated grammar

# (synth-fun ps ( (tmp14 Int) (arg Int) ) Bool
#  ((B Bool) (C Bool) (D Bool) (E Int) (F Int))
#  ((B Bool ((or C D)))
#  (C Bool ((>= F arg)))
#  (D Bool ((= E (sum_n (- arg F)))))
#  (E Int (tmp14))
#  (F Int (1))))

# (synth-fun inv0 ((tmp1 Int) (tmp2 Int) (arg Int) ) Bool
#    ((B Bool) (C Bool) (D Bool) (E Int) (F Int))
#    ((B Bool ((or C D)))
#    (C Bool ((>= 1 arg) ))
#    (D Bool ((and (>= E 1) (<= E arg) (= E (sum_n (- E F))))))
#    (E Int (tmp1 tmp2))
#    (F Int (1))))

def grammar(ci: CodeInfo):
  name = ci.name

  if name.startswith("inv"):
    f = Choose(IntLit(1))
    e = Choose(*ci.modifiedVars)
    d = And(Ge(e, IntLit(1)), And(Le(e, ci.readVars[0]), Eq(e, Call("sum_n", Int(), Sub(e, f)))))
    c = Ge(IntLit(1), ci.readVars[0])
    b = Or(c, d)

    return Synth(ci.name, b, *ci.modifiedVars, *ci.readVars)

  else:  # ps
    arg = ci.readVars[0]
    rv = ci.modifiedVars[0]

    choices = Choose(IntLit(1), IntLit(2), IntLit(3))
    b = Or(Ge(choices, arg), Eq(rv, Call("sum_n", Int(), Sub(arg, choices))))
    return Synth(name, b, *ci.modifiedVars, *ci.readVars)

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

  #rosette synthesizer  + CVC verfication
  candidates = synthesize(basename,lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath)
  print("====== verified candidates")
  for c in candidates:print(c,"\n")

  #TODO codegen

