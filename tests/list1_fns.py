import os
import sys

from analysis import CodeInfo, analyze
from ir import Choose, And, Ge, Eq, Le, Sub, Synth, Call, Int, IntLit, FnDecl, Var, Add, Ite, List, Gt, Bool, Lt, Fn
from synthesize_rosette import synthesize
from rosette_translator import toRosette

# # programmatically generated grammar
def grammar(ci: CodeInfo):
  name = ci.name

  if name.startswith("inv"):

    f = Choose(Call("Select-pred", Fn(Bool(), *ci.readVars)),Call("Select-pred1", Fn(Bool(), *ci.readVars)),Call("Select-pred2", Fn(Bool(), *ci.readVars)))
    a = Choose(ci.modifiedVars[0], *ci.readVars, Call("Select",List(Int()),*ci.readVars,f))
    i = Choose(IntLit(0), IntLit(1))
    e = Choose(Call("list_eq",Bool(),Call('list_append',List(Int()),a,Call("Select", List(Int()), Call('list_tail', List(Int()),a,ci.modifiedVars[1]),f)),a), Call("list_eq",Bool(),Call('list_concat',List(Int()),a, Call('list_tail', List(Int()),a,ci.modifiedVars[1])),a))
    d = Choose(Ge(ci.modifiedVars[1],Call("list_length",Int(),*ci.readVars)),Le(ci.modifiedVars[1],Call("list_length",Int(),*ci.readVars)),Gt(ci.modifiedVars[1],Call("list_length",Int(),*ci.readVars)),Lt(ci.modifiedVars[1],Call("list_length",Int(),*ci.readVars)), Eq(ci.modifiedVars[1],Call("list_length",Int(),*ci.readVars)))
    c = Choose(Ge(ci.modifiedVars[1],i),Le(ci.modifiedVars[1],i),Gt(ci.modifiedVars[1],i),Lt(ci.modifiedVars[1],i), Eq(ci.modifiedVars[1],i))
    b = Choose(And(And(c,d),e))
    return Synth(ci.name, b, *ci.modifiedVars, *ci.readVars)

  else:  # ps
    rv = ci.modifiedVars[0]
    fns = Choose(Call("Select-pred", Fn(Bool(), rv)),Call("Select-pred1", Fn(Bool(), rv)),Call("Select-pred2", Fn(Bool(), rv)))
    choices  = Choose(Call("list_eq", Bool(), rv, *ci.readVars), (Call("list_eq", Bool(), rv, Call("Select", List(Int()),*ci.readVars,fns))))
    
    return Synth(name, choices, *ci.modifiedVars, *ci.readVars)


def targetLang():
  
  arg = Var("n",Int())
  select_pred = FnDecl("Select-pred",Fn(Bool()),Gt(arg,2),arg)
  select_pred1 = FnDecl("Select-pred1",Fn(Bool()),Lt(arg,10),arg)
  select_pred2 = FnDecl("Select-pred2",Fn(Bool()),And(Gt(arg,2),Lt(arg,10)),arg)
  data = Var("l", List(Int()))
  f = Var("f", Fn(Bool()))
  select_func = FnDecl("Select", List(Int()), Ite(Eq(Call("list_length",Int(),data),IntLit(0)), Call("list_empty",List(Int())), Ite(Call(f.args[0],Bool(),Call("list_get", Int(), data, IntLit(0))),Call("list_append",List(Int()),Call("Select",List(Int()),Call("list_tail", List(Int()),data, IntLit(1))), Call("list_get", Int(),data, IntLit(0)),),Call("Select",List(Int()),Call("list_tail",List(Int()),data,IntLit(1))))),data,f)
  

  
  return [select_pred,select_pred1, select_pred2, select_func]


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
  # toRosette(basename+".rkt",lang,vars, invAndPs, preds, vc, loopAndPsInfo,[])

  candidates = synthesize(basename,lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath)
  print("====== verified candidates")
  for c in candidates:print(c,"\n")

