import os
import sys

from analysis import CodeInfo, analyze
from ir import Choose, And, Ge, Eq, Le, Sub, Synth, Call, Int, IntLit, Or, FnDecl, Var, Add, Ite

if True:
  from synthesize_rosette import synthesize
else:
  from synthesis import synthesize_new as synthesize

# # programmatically generated grammar
    # (synth-fun inv0 ((tmp Int) (tmp1 Int) ) Bool
    #    ((B Bool) (C Bool) (D Bool) (E Int) (F Int))
    #    ((B Bool ((and C D)))
    #    (C Bool ((= E (sum_n (- E F)))))
    #    (D Bool ((and (>= E F) (<= E F))))
    #    (E Int (tmp tmp1))
    #    (F Int (1 2 3))))
   # (synth-fun ps ( (tmp12 Int) ) Bool
    #  ((B Bool) (C Int) (D Int))
    #  ((B Bool ((= C (sum_n D))))
    #  (C Int (tmp12))
    #  (D Int (1 2))))
def grammar(ci: CodeInfo):
  name = ci.name

  if name.startswith("inv"):

    e = Choose(*ci.modifiedVars)
    f = Choose(IntLit(1), IntLit(2), IntLit(3))
    c = Eq(e, Call("sum_n", Int(), Sub(e, f)))
    d = And(Ge(e, f), Le(e, f))
    b = And(c, d)
    return Synth(ci.name, b, *ci.modifiedVars, *ci.readVars)


  else:  # ps
    rv = ci.modifiedVars[0]
    choices = Choose(IntLit(1), IntLit(2))
    b = Eq(rv, Call("sum_n", Int(), choices))
    return Synth(name, b, *ci.modifiedVars, *ci.readVars)



def targetLang():
  x = Var("x", Int())
  sum_n = FnDecl("_sum_n", Int(), Ite(Ge(x, IntLit(1)), Add(x, Call("_sum_n", Int(), Sub(x, IntLit(1)))), IntLit(0)), x)
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
  for c in candidates:
    print(c,"\n")
