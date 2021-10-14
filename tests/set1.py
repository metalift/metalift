import os
import sys

from analysis import CodeInfo, analyze
from ir import Choose, And, Or, Not, Gt, Ge, Eq, Le, Le, Sub, Synth, Call, Int, IntLit, BoolLit, FnDecl, Var, Add, Implies, Ite
from synthesis import synthesize_new

def grammar(ci: CodeInfo):
  name = ci.name

  if name.startswith("inv"):
    raise Exception("no invariant")
  else:  # ps
    inputVars = Choose(*ci.readVars)
    outputVar = ci.modifiedVars[0]
    boolLit = Choose(BoolLit(False), BoolLit(True))
    intLit = Choose(IntLit(0), IntLit(1), IntLit(2), IntLit(3))
    comp = Eq(inputVars, intLit)
    ite = boolLit
    for i in range(3):
      ite = Choose(ite, Ite(comp, boolLit, ite))
    summary = Eq(outputVar, ite)
    return Synth(name, summary, *ci.modifiedVars, *ci.readVars)

def targetLang():
  return []

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
