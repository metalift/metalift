import os
import sys

from analysis import CodeInfo, analyze
from ir import Choose, And, Or, Not, Gt, Ge, Eq, Le, Le, Sub, Synth, Call, Int, IntLit, FnDecl, Var, Add, Implies, Ite
from rosette_translator import toRosette
from synthesize_rosette import synthesize

def grammar(ci: CodeInfo):
  name = ci.name

  if name.startswith("inv"):
    raise Exception("no invariant")
  else:  # ps
    
    outputVar = ci.modifiedVars[0]
    intLit = Choose(IntLit(1), IntLit(2), IntLit(3), IntLit(10))
    cond = Choose(
      Eq(*ci.readVars, intLit),
      Gt(*ci.readVars, intLit),
      Le(*ci.readVars, intLit)
    )
    ite = Ite(cond, intLit, intLit)
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
  candidates = synthesize(basename,lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath)
  for c in candidates:print(c,"\n")
  # candidates = synthesize_new(lang, invAndPs, vars, preds, vc, cvcPath, basename)
